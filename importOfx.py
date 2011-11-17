#!/usr/bin/python

import warnings
import sys, os, time, re
import argparse
from BeautifulSoup import *
from gnucash import Session, Account, Transaction, Split, GncPrice, GncNumeric, GncCommodity, GncLot
from gnucash.gnucash_core_c import gnc_quote_source_lookup_by_internal, \
     gnc_commodity_equal, gnc_price_create
from datetime import datetime, timedelta
from gnucash.gnucash_core_c import ACCT_TYPE_BANK, ACCT_TYPE_CASH, \
     ACCT_TYPE_STOCK, ACCT_TYPE_MUTUAL, ACCT_TYPE_INCOME, ACCT_TYPE_EXPENSE

from bisect import bisect_right
from decimal import Decimal
from math import log10

ZERO = Decimal(0)

def gnc_numeric_to_python_Decimal(numeric):
    negative = numeric.negative_p()
    if negative:
        sign = 1
    else:
        sign = 0
    copy = GncNumeric(numeric.num(), numeric.denom())
    result = copy.to_decimal(None)
    if not result:
        raise Exception("gnc numeric value %s can't be converted to Decimal" %
                        copy.to_string() )
    digit_tuple = tuple( int(char)
                         for char in str(copy.num())
                         if char != '-' )
    denominator = copy.denom()
    exponent = int(log10(denominator))
    assert( (10 ** exponent) == denominator )
    return Decimal( (sign, digit_tuple, -exponent) )

def gnc_numeric_from_decimal(decimal_value):
    sign, digits, exponent = decimal_value.as_tuple()

    # convert decimal digits to a fractional numerator
    # equivlent to
    # numerator = int(''.join(digits))
    # but without the wated conversion to string and back,
    # this is probably the same algorithm int() uses
    numerator = 0
    TEN = int(Decimal(0).radix()) # this is always 10
    numerator_place_value = 1
    # add each digit to the final value multiplied by the place value
    # from least significant to most sigificant
    for i in xrange(len(digits)-1,-1,-1):
        numerator += digits[i] * numerator_place_value
        numerator_place_value *= TEN

    if decimal_value.is_signed():
        numerator = -numerator

    # if the exponent is negative, we use it to set the denominator
    if exponent < 0 :
        denominator = TEN ** (-exponent)
    # if the exponent isn't negative, we bump up the numerator
    # and set the denominator to 1
    else:
        numerator *= TEN ** exponent
        denominator = 1

    return GncNumeric(numerator, denominator)

# ofxfile=sys.argv[0]
# gcfile=sys.argv[1]

# This script expects your accounts to be setup like this
#
# Assets:Investments:Ameritrade.com
# Assets:Investments:Ameritrade.com:Cash 123445678
# Assets:Investments:Ameritrade.com:Stocks:MSFT
# Assets:Investments:Ameritrade.com:Mutual Funds:BEARX
#
# The Brokerage account code has to match <ORG> tag of the OFX
# file (case sensitive)... The Cash account code (note its code not name)
# has to match <INVFROM><ACCID> tag, its usually account number of cash or
# margin account
#
# Reason we match by account code, is so that you can adjust the name of
# account and still have it updated.

brokerage_account_root = 'Assets:Investments'
# set to empty strings if want commodity ticker accounts directly
# under the brokerage account
brokerage_account_stocks = 'Stocks';
brokerage_account_mutual_funds = 'Mutual Funds'
brokerage_account_bonds = 'Bonds'
brokerage_account_options = 'Options'
# Account for broker commissions and fees
commissions_account = 'Expenses:Commissions'
# Income account roots. We have a separate sub-tree for
# income with tax-exempt flag set.
income_account_root = 'Income'
income_account_tax_exempt_root = 'Income:Tax Exempt'
# The elements of the tuple are. The actual account will be under
# income_account_root, or under income_account_tax_exempt_root if
# tax_exempt_flag is set
# 
# 1. long term cap gains
# 2. Short Term cap gains
# 3. Dividend Income
# 4. Interest Income
# 5. All other income
income_type_accounts = ('Long Term Capital Gains', 'Short Term Capital Gains',
                        'Dividend Income', 'Interest Income', 'Misc Income',
                        'Futures P&L')

# When OFX file has a position in some stock or mutual fund and after
# processing and inserting buy/sell transactions GnuCash position does
# not agree, we will generate an adjustment.. This happens when you
# first time import OFX file that shows some long-held position, ie
# you initial holdings.. Or when you did not download OFX file for a
# long time, and some buys and sells got lost.
#
# If the final shares amount does not agree, we will generate the adjustment.
# If GnuCash shares is zero, it means its initial position that had came
# from somewhere, otherwise its some buys and sells that are missing.
#
# In case of initial position, below variables control which account
# the adjustment comes from. 'cash' means from the
# Assets:Investment:Brokername:Cash, (which will create a debit
# there, which you will have to make up by giving that account initial
# money from equity).  'equity' means money will come from
# Equity:Opening Balances directly.. Anything else means it will be
# unbalanced(ie come from Unbalanced-USD) and you will have to put in
# correct account manually

# True to auto-create the root brokerage account
auto_create_brokerage_accounts = True
# True to auto-create commodities accounts
auto_create_commodity_accounts = True
# True to auto-create income and expanse accounts, for example
# by default Income:Capital Gains and Income:Tax Exempt tree
# does not exist
auto_create_income_and_expanse_accounts = True
# True to import prices of securities from POSLIST
auto_create_prices = True

#----------------
# Data Model
#----------------

class OfxElement:
  def __init__(self, soup):
    for name in [c[0] for c in self.children]:
      self.__setattr__(name, None)
    #print >> sys.stderr, "%s.__init__(soup):" % (self)
    self.parse(soup)

  def parse(self, soup):
    #print >> sys.stderr, "%s.parse" % (self)
    for c in self.children:
      if isinstance(c, str):
        recursive = False
        required = True
        if c[0] == '*':
          c = c[1:]
          recursive = True
        if c[0] == '?':
          c = c[1:]
          required = False
        #print "Here finding %s, recursive=%s, required=%s " % (c, recursive, required)
        tmp = soup.find(c, recursive=recursive)
        if tmp is None and required:
          raise RuntimeError("""--%s-- Required attribute %s missing -----
%s
--------------------------------------------------------------""" % (self.__class__.__name__, c, soup.prettify()))
        elif tmp is not None:
          soup = tmp
        else:
          soup = BeautifulSoup()
        continue
      type,required,ofxName,isList = (str, True, None, False)
      name,c = c[0], c[1:]
      if c: (type,c) = c[0],c[1:]
      if c: (required,c) = c[0],c[1:]
      if c: (ofxName,c) = c[0],c[1:]
      if c: (isList,c) = c[0],c[1:]
      if ofxName is None:
        ofxName = name.lower()
      if isinstance(type, str):
        type = globals()[type]
      recursive = False
      if ofxName is not True and ofxName[0]=='*':
        ofxName=ofxName[1:]
        recursive = True

      #print "name=%s type=%s ofxName=%s required=%s" % (name, type, ofxName, required)
      #print 'here1 ofxName=%s soup=%s' % (ofxName, soup)
      elems = soup.findAll(lambda tag: ofxName is True or tag.name == ofxName, recursive=recursive)
      #print "here2 found=%s" % (elem)
      if len(elems) == 0: 
        if required:
          raise RuntimeError("""--%s-- Required attribute %s missing -----
%s
--------------------------------------------------------------""" % (self.__class__.__name__, ofxName, soup.prettify()))
        elif isList:
          self.__setattr__(name, [])
      elif len(elems) > 1 and not isList:
          raise RuntimeError("""--%s-- More then one %s element while parsing  -----
%s
--------------------------------------------------------------""" % (self.__class__.__name__, ofxName, soup.prettify()))
      else:
        result = None
        if isList:
          result = []
        for elem in elems:
          #print "Here3 type=%s subclass=%s" % (type, issubclass(type, OfxElement))
          if isinstance(type, types.FunctionType):
            elem = type(elem);
          elif isinstance(type, bool):
            elem = type(elem.text.encode())
            if len(elem) > 0 and elem[0] == "Y" or elem[0] == "y":
              elem = True
            else:
              elem = False
          elif issubclass(type, OfxElement):
            #print "Here4 type=%s elem=%s" % (type, elem)
            elem = type(elem)
          elif issubclass(type, datetime):
            elem = convertOfxDateTime(elem.text.encode())
          else:
            #print "Here5 type=%s elem=%s" % (type, elem.text.encode())
            elem = type(elem.text.encode())
          if isList:
            if elem is not None:
              result.append(elem)
          else:
            result = elem
        self.__setattr__(name,result)


def ofxClassToString(self):
  ret = "<" + self.__class__.__name__ + " "
  first = True
  for name in [c[0] for c in self.children]:
    value = self.__getattribute__(name)
    if value is not None:
      value = str(value)
      if len(value) > 20: value = "..."
      if not first: ret += ","
      ret += name + ":" + str(value)
      first = False
  ret += ">"
  return ret


def makeOfxClass(name, *elements):
  """Dynamically define class NAME(OfxElement) and assign rest of the parameters
  to CHILDREN class variable"""
  globals()[name] = type(name, (OfxElement,object), {'children': elements,
                                                   '__str__': lambda self: ofxClassToString(self),
                                                   '__repr__': lambda self: ofxClassToString(self)})
    

makeOfxClass('Ofx', ('signonResponse', 'SignOnResponse', True, '*sonrs'),
             ('stmtResponse', 'InvestmentStatementResponse', True, '*invstmttrnrs' ),
             "*?seclist",
             ('secList', 'parseSecurityInfo', False, True, True))

# makeOfxClass('SignOnMsgSet', ('response', 'SignOnResponse', True, 'sonrs'))

makeOfxClass('SignOnResponse', ('status', 'TransactionStatus', True),
             ('orgName',str,True, '*org'),
             ('time', datetime, True, 'dtserver'),
             ('language', str, False, 'language'))

makeOfxClass('TransactionStatus',
             ('code', int, True),
             ('severity',),
             ('message',str,False))

# makeOfxClass('FinancialInstitution', ('orgName', str, True, 'org'))
    
# makeOfxClass('InvestmentStatementMsgSet',
#              ("investmentStatementResponseTransaction",
#               "InvestmentStatementResponseTransaction", True, 'invstmttrnrs'))

makeOfxClass('InvestmentStatementResponse',
             ('status', 'TransactionStatus', True, 'status'),
             "invstmtrs",
             ('timeAsOf', datetime, True, 'dtasof'),
             ('currencyCode', str, True, 'curdef'),
             ('investmentAccountFrom', 'InvestmentAccountDetails', True, '*invacctfrom'),
             ('transactions', 'InvestmentTransactionList', True, '*invtranlist'),
             '*?invposlist',
             ('positions', 'parseInvestmentPosList', False, True, True))

makeOfxClass('InvestmentAccountDetails',
             ('brokerId', str, True, "brokerid"),
             ('accountId', str, True, "acctid"),
             ('accountKey', str, False, "acctkey"))

makeOfxClass('InvestmentAccountDetails',
             ('brokerId', str, True, "brokerid"),
             ('accountId', str, True, "acctid"),
             ('accountKey', str, False, "acctkey"))

makeOfxClass('InvestmentTransactionList',
             ('startTime', datetime, True, 'dtstart'),
             ('endTime', datetime, True, 'dtend'),
             ('bankTransactions', 'BankTransaction', False, 'invbanktran', True),
             ('investmentTransactions', 'parseInvestmentTransaction', False, True, True))


makeOfxClass('InvestmentPositionList',
             ('startTime', datetime, True, 'dtstart'),
             ('endTime', datetime, True, 'dtend'),
             ('bankTransactions', 'BankTransaction', False, 'invbanktran', True),
             ('investmentTransactions', 'parseInvestmentTransaction', False, True, True))

makeOfxClass('BankTransaction',
             ('subAccountFund', str, True, 'subacctfund'),
             ('transaction', 'OfxTransaction', True, 'stmttrn'))

makeOfxClass('OfxTransaction', ('type', str, True, 'trntype'),
              ('timePosted', datetime, True, 'dtposted'),
              ('timeInitiated', datetime, False, 'dtuser'),
              ('timeAvailable', datetime, False, 'dtavail'),
              ('amount', Decimal, True, 'trnamt'),
              ('transactionId', str, True, 'fitid'),
              ('correctionId', str, False, 'correctfitid'),
              ('correctionAction', str, False, 'correctaction'),
              ('serverId', str, False, 'srvrtid'),
              ('checkNumber', str, False, 'checknum'),
              ('refNumber', str, False, 'refnum'),
              ('standardIndustrialCode', str, False, 'sic'),
              ('payeeId', str, False, 'payeeid'),
              ('name', str, False, 'name'),
              ('bankAccountTo', 'BankAccountDetails', False, 'bankacctto'),
              ('creditCardAccountTo', 'BankAccountDetails', False, 'ccacctto'),
              ('memo', str, False, 'memo'),
              ('currency', 'OfxCurrency', False, 'currency'))


makeOfxClass('BankAccountDetails', ('bankId', str, True, 'bankid'),
              ('branchId', str, False, 'branchid'),
              ('accountId', str, True, 'acctid'),
              ('accountType', str, False, 'accttype'),
              ('accountKey', str, False, 'acctkey'))
            

makeOfxClass('BaseInvestmentTransaction', ('transactionId', str, True, 'fitid'),
              ('serverId', str, False, 'srvrtid'),
              ('tradeDate', datetime, True, 'dttrade'),
              ('settlementDate', datetime, False, 'dtsettle'),
              ('reversalTransactionId', str, False, 'reversalfitid'),
              ('memo', str, False, 'memo'))


# handles both INVBUY and INVSELL, since SELL has more fields
# but they are all optional
makeOfxClass('BuyOrSellInvestmentTransaction',
             ('invTran', 'BaseInvestmentTransaction', True, 'invtran'),
              ('securityId', 'SecurityId', True, 'secid'),
              ('units', Decimal, True, 'units'),
              ('unitPrice', Decimal, True, 'unitprice'),
              ('markup', Decimal, False, 'markup'),
              ('commission', Decimal, False, 'commission'),
              ('taxes', Decimal, False, 'taxes'),
              ('fees', Decimal, False, 'fees'),
              ('load', Decimal, False, 'load'),
              ('withholding', Decimal, False, 'withholding'),
              ('statewithholding', Decimal, False, 'statewithholding'),
              ('penalty', Decimal, False, 'penalty'),
              ('taxExempt', bool, False, 'taxexempt'),
              ('total', Decimal, True, 'total'),
              ('gain', Decimal, False, 'gain'),
              ('currencyCode', str, False, 'currency'),
              ('originalCurrency', 'OfxCurrency', False, 'origcurrency'),
              ('subAccountSecurity', str, False, 'subacctsec'),
              ('subAccountFund', str, False, 'subacctfund'),
              ('loadid', str, False, 'loanid'),
              ('inv401kSource', str, False, 'inv401ksource'))

makeOfxClass('SecurityId',
             ('uniqueId', str, True, 'uniqueid'),
             ('uniqueIdType', str, True, 'uniqueidtype'))

makeOfxClass('OfxCurrency', ('currencyRate', Decimal, True, 'currate'),
              ('currencyCode', str, True, 'cursym'))

#buymf
makeOfxClass('BuyMFTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invbuy'),
              ('type', str, True, 'buytype'))

#sellmf
makeOfxClass('SellMFTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invsell'),
             ('type', str, True, 'selltype'))

#buydebt
makeOfxClass('BuyDebtTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invbuy'),
             # Gets the amount of accrued interest on the debt. This
             # is an optional field according to the OFX spec.
             ('accruedInterest', Decimal, False, 'accrdint'))

#selldebt
makeOfxClass('SellDebtTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invsell'),
             # Gets the reason for the sale. One of "CALL" (the debt
             # was called), "SELL" (the debt was sold), "MATURITY"
             # (the debt reached maturity).
             ('sellReason', str, False, 'sellreason'),
             # Gets the amount of accrued interest on the debt. This
             # is an optional field according to the OFX spec.
             ('accruedInterest', Decimal, False, 'accrdint'))

#buyopt
makeOfxClass('BuyOptionTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invbuy'),
             # Gets the type of option purchase (i.e. "BUYTOOPEN" or
             # "BUYTOCLOSE"). This is a required field according to
             # the OFX spec.
             ('type', str, True, 'optbuytype'),
             # Gets the number of shares per option contact. This is a
             # required field according to the OFX spec.
             ('sharesPerContract', int, True, 'shperctrct'))

#sellopt
makeOfxClass('SellOptionTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invsell'),
             # Gets the type of option sale (i.e. "SELLTOCLOSE" or
             # "SELLTOOPEN"). This is a required field according to
             # the OFX spec.
             ('type', str, True, 'optselltype'),
             # Gets the number of shares per option contact. This is a
             # required field according to the OFX spec.
             ('sharesPerContract', int, True, 'shperctrct'),
             # Sets a related transaction for the option sale for
             # complex option transactions. This is an optional field
             # according to the OFX spec.
             ('relatedTransactionId', str, False, 'relfitid'),
             # Gets the type for the related transaction. One of
             # "SPREAD", "STRADDLE", "NONE", "OTHER". This is an
             # optional field according to the OFX spec.
             ('relatedType', str, False, 'reltype'),
             # Gets how the options position is secured (for short
             # positions. One of: NAKED or COVERED
             ('secured', str, False, 'secured'))

#buyother
makeOfxClass('BuyOtherTransaction',
            ('investment', 'BuyOrSellInvestmentTransaction', True, 'invbuy'))

#sellother
makeOfxClass('SellOtherTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invsell'))

#buystock
makeOfxClass('BuyStockTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invbuy'),
             # Gets the type of stock purchase (i.e. "BUY" or
             # "BUYTOCOVER"). This is a required field according to
             # the OFX spec.
             ('type', str, True, 'buytype'))

#sellstock
makeOfxClass('SellStockTransaction',
             ('investment', 'BuyOrSellInvestmentTransaction', True, 'invsell'),
             # Gets the type of stock sale (i.e. "SELL" or
             # "SELLSHORT"). This is a required field according to the
             # OFX spec.
             ('type', str, True, 'selltype'))


#transfer
makeOfxClass('TransferTransaction',
             ('invTran', 'BaseInvestmentTransaction', True, 'invtran'),
             ('securityId', 'SecurityId', True, 'secid'),
             # Gets the sub-account type. One of "CASH", "MARGIN",
             # "SHORT", "OTHER". 
             ('subAccountSec', str, False, 'subacctsec'),
             # Gets the number of units of the security that was
             # transferred. For security-based actions other than
             # stock splits, this is the quantity bought. For stocks,
             # mutual funds, and others, this is the number of
             # shares. For bonds, this is the face value. For options,
             # this is the number of contacts. This is a required
             # field according to the OFX spec.
             ('units', Decimal, True, 'units'),
             # Gets the type of transfer. One of "IN" or "OUT". This
             # is a required field according to the OFX spec.
             ('unitPrice', Decimal, False, 'unitprice'),
             ('purchaseDate', datetime, False, 'dtpurchase'),
             ('transferAction', str, True, 'tferaction'),
             # Gets the position type. One of SHORT or LONG. This is a
             # required field according to the OFX spec.
             ('type', str, True, 'postype'),
             ('averageCostBasis', Decimal, False, 'avgcostbasis'),
             ('inv401kSource', str, False, 'inv401ksource'))

makeOfxClass('MarginInterestTransaction',
             ('invTran', 'BaseInvestmentTransaction', True, 'invtran'),
             ('subAccountFund', str, False, 'subacctfund'),
             ('subAccountSec', str, False, 'subacctsec'),
             ('total', Decimal, True, 'total'),
             ('currencyCode', str, False, 'currency'),
             ('originalCurrency', 'OfxCurrency', False, 'origcurrency'))

makeOfxClass('IncomeTransaction',
             ('invTran', 'BaseInvestmentTransaction', True, 'invtran'),
             ('securityId', 'SecurityId', True, 'secid'),
             # Long or short term capital gains, dividends, or misc
             # "CGLONG", CGSHORT", "DIV", "INTEREST", "MISC"
             ('incomeType', str, True, 'incometype'),
             ('subAccountFund', str, False, 'subacctfund'),
             ('subAccountSec', str, False, 'subacct'),
             ('total', Decimal, True, 'total'),
             ('taxExempt', bool, False, 'taxexempt'),
             ('withholding', Decimal, False, 'withholding'),
             ('currencyCode', str, False, 'currency'),
             ('originalCurrency', 'OfxCurrency', False, 'origcurrency'),
             ('inv401kSource', str, False, 'inv401ksource'))

makeOfxClass('ExpenseTransaction',
             ('invTran', 'BaseInvestmentTransaction', True, 'invtran'),
             ('securityId', 'SecurityId', True, 'secid'),
             # Long or short term capital gains, dividends, or misc
             # "CGLONG", CGSHORT", "DIV", "INTEREST", "MISC"
             ('subAccountFund', str, False, 'subacctfund'),
             ('subAccountSec', str, False, 'subacct'),
             ('total', Decimal, True, 'total'),
             ('currencyCode', str, False, 'currency'),
             ('originalCurrency', 'OfxCurrency', False, 'origcurrency'),
             ('inv401kSource', str, False, 'inv401ksource'))

def parseInvestmentTransaction(soup):
  if soup.name == 'buymf':
    return BuyMFTransaction(soup)
  elif soup.name == 'sellmf':
    return SellMFTransaction(soup)
  elif soup.name == 'buyopt':
    return BuyOptionTransaction(soup)
  elif soup.name == 'sellopt':
    return SellOptionTransaction(soup)
  elif soup.name == 'buyother':
    return BuyOtherTransaction(soup)
  elif soup.name == 'sellother':
    return SellOtherTransaction(soup)
  elif soup.name == 'buystock':
    return BuyStockTransaction(soup)
  elif soup.name == 'sellstock':
    return SellStockTransaction(soup)
  elif soup.name == 'margininterest':
    return MarginInterestTransaction(soup)
  elif soup.name == 'income':
    return IncomeTransaction(soup)
  elif soup.name == 'invexpense':
    return ExpenseTransaction(soup)
  elif soup.name == 'transfer':
    return TransferTransaction(soup)
  elif soup.name in ('dtstart', 'dtend', 'invbanktran'):
    return None
  else: 
    print "Unknown investment transaction %s" % (soup.name)
    return None

makeOfxClass('SecurityInfo',
             ('securityId', 'SecurityId', True, 'secid'),
             ('securityName', str, True, 'secname'),
             ('ticker', str, False, 'ticker'),
             ('fiId', str, False, 'fiid'),
             ('rating', str, False, 'rating'),
             ('unitPrice', Decimal, False, 'unitprice'),
             ('timeAsOf', datetime, False, 'dtasof'),
             ('currencyCode', str, False, 'currency'),
             ('memo', str, False, 'memo'))

# debtinfo
makeOfxClass('DebtSecurityInfo',
             ('securityInfo', 'SecurityInfo', True, 'secinfo'),
             ('parValue', Decimal, True, 'parvalue'),
             # Gets the type of debt. One of "COUPON" or "ZERO". This
             # is a required field according to the OFX spec.
             ('type', str, True, 'debttype'),
             # Gets the class of debt. One of "TREASURY", "MUNICIPAL",
             # "CORPORATE", or "OTHER". This is an optional field
             # according to the OFX spec.
             ('debtClass', str, False, 'debtclass'),
             # Gets the coupon rate of the debt for the next closest
             # call date. This is an optional field according to the
             # OFX spec.
             ('couponRate', Decimal, False, 'couponrt'),
             # Gets the coupon rate of the debt for the next closest
             # call date. This is an optional field according to the
             # OFX spec.
             ('nextMaturityDate', datetime, False, 'dtcoupon'),
             # Gets the coupon frequency. One of "MONTHLY",
             # "QUARTERLY", "SEMIANNUAL", "ANNUAL", or "OTHER". This
             # is an optional field according to the OFX spec.
             ('couponFrequency', str, False, 'couponfreq'),
             # Gets the bond price. This is an optional field
             # according to the OFX spec.
             ('callPrice', Decimal, False, 'callprice'),
             # Gets the yield to call as a rate. This is an optional
             # field according to the OFX spec.
             ('yieldToCall', Decimal, False, 'yieldtocall'),
             # Gets the next call date. This is an optional field
             # according to the OFX spec.
             ('nextCallDate', datetime, False, 'dtcall'),
             # Gets the type of call. "CALL", "PUT", "PREFUND", "MATURITY"
             ('callType', str, False, 'calltype'),
             # Gets the yield to maturity as a rate. This is an
             # optional field according to the OFX spec.
             ('yieldToMaturity', Decimal, False, 'yieldtomat'),
             # Sets the date when the debt matures. This is an
             # optional field according to the OFX spec.
             ('maturityDate', datetime, False, 'dtmat'),
             # Asset class, one of: "DOMESTICBOND", "INTLBOND", "LARGESTOCK",
             # "SMALLSTOCK", "INTLSTOCK", "MONEYMARKET", "OTHER", optional
             ('assetClass', str, False, 'assetclass'))

DebtSecurityInfo.commodityNamespace = 'AMEX'

# mfinfo
makeOfxClass('MutualFundSecurityInfo',
             ('securityInfo', 'SecurityInfo', True, 'secinfo'),
             # Gets the mutual fund type. One of "OPENEND",
             # "CLOSEEND", or "OTHER". This is an optional field
             # according to the OFX spec.
             ('type', str, False, 'mftype'),
             # Gets the yield as a rate. This is an optional field
             # according to the OFX spec.
             ('yield', Decimal, False, 'yield'),
             # Gets the as-of date for the yield. This is an optional
             # field according to the OFX spec.
             ('dateYieldAsOf', datetime, False, 'dtyieldasof'))

MutualFundSecurityInfo.commodityNamespace = 'FUND'

# optinfo
makeOfxClass('OptionSecurityInfo',
             ('securityInfo', 'SecurityInfo', True, 'secinfo'),
             # Gets the type of option. One of "PUT" or "CALL". This
             # is a required field according to the OFX spec.
             ('type', str, True, 'opttype'),
             # Gets the strike price of the option. This is a required
             # field according to the OFX spec.
             ('strikePrice', Decimal, True, 'strikeprice'),
             # Gets the expiration date of the option. This is a
             # required field according to the OFX spec.
             ('expirationDate', datetime, True, 'dtexpire'),
             # Gets the number of shares per option contact. This is a
             # required field according to the OFX spec.
             ('sharesPerContract', int, True, 'shperctrct'),
             # Gets the security id of the underling security. This is
             # an optional field according to the OFX spec.
             ('underlyingSecurity', 'SecurityId', False, 'secid'))

OptionSecurityInfo.commodityNamespace = 'AMEX'


# otherinfo
makeOfxClass('OtherSecurityInfo',
             ('securityInfo', 'SecurityInfo', True, 'secinfo'),
             # Gets a description of the type of security. This is an
             # optional field according to the OFX spec.
             ('type', str, False, 'typedesc'),
             # Asset class, one of: "DOMESTICBOND", "INTLBOND", "LARGESTOCK",
             # "SMALLSTOCK", "INTLSTOCK", "MONEYMARKET", "OTHER", optional
             ('assetClass', str, False, 'assetclass'),
             # Gets the FI-defined asset class of the debt. This is an
             # optional field according to the OFX spec.
             ('fiAssetClass', str, False, 'fiassetclass'))

OtherSecurityInfo.commodityNamespace = 'AMEX'

# stockinfo
makeOfxClass('StockSecurityInfo',
             ('securityInfo', 'SecurityInfo', True, 'secinfo'),
             # Gets the type of stock. One of "COMMON", "PREFERRED",
             # "CONVERTIBLE", or "OTHER". This is an optional field
             # according to the OFX spec.
             ('type', str, False, 'stocktype'),
             # Gets the current yield reported as the dividend
             # expressed as a portion of the current stock price, a
             # rate. This is an optional field according to the OFX
             # spec.
             ('yield', Decimal, False, 'yield'),
             # Gets the as-of date for the yield. This is an optional
             # field according to the OFX spec.
             ('dateYieldAsOf', datetime, False, 'dtyieldasof'),
             # Asset class, one of: "DOMESTICBOND", "INTLBOND", "LARGESTOCK",
             # "SMALLSTOCK", "INTLSTOCK", "MONEYMARKET", "OTHER", optional
             ('assetClass', str, False, 'assetclass'),
             # Sets the FI-defined asset class of the stock. This is
             # an optional field according to the OFX spec.
             ('fiAssetClass', str, False, 'fiassetclass'))

StockSecurityInfo.commodityNamespace = 'AMEX'


def parseSecurityInfo(soup):
  if soup.name == 'debtinfo':
    return DebtSecurityInfo(soup)
  elif soup.name == 'optinfo':
    return OptionSecurityInfo(soup)
  elif soup.name == 'otherinfo':
    return OtherSecurityInfo(soup)
  elif soup.name == 'mfinfo':
    return MutualFundSecurityInfo(soup)
  elif soup.name == 'stockinfo':
    return StockSecurityInfo(soup)
  else: 
    print "Unknown security info %s" % (soup.name)
    return None


# invpos
makeOfxClass('InvestmentPosition',
             ('securityId', 'SecurityId', True, 'secid'),
             # Gets the sub-account type. One of "CASH", "MARGIN",
             # "SHORT", "OTHER". This is a required field according to
             # the OFX spec.
             ('heldInAccount', str, True, 'heldinacct'),
             # Gets the position type. One of SHORT or LONG. This is a
             # required field according to the OFX spec.
             ('type', str, True, 'postype'),
             # Gets the number of units in the position. For stocks,
             # mutual funds, and others, this is the number of
             # shares. For bonds, this is the face value. For options,
             # this is the number of contacts. This is a required
             # field according to the OFX spec.
             ('units', Decimal, True, 'units'),
             # Gets the price per commonly-quoted unit. For stocks,
             # mutual funds, and others, this is the share price. For
             # bonds, this is the percentage of par. For options, this
             # is the per share (not per contact) price. This is a
             # required field according to the OFX spec.
             ('unitPrice', Decimal, True, 'unitprice'),
             # Gets the market value of this position. This is a
             # required field according to the OFX spec.
             ('marketValue', Decimal, True, 'mktval'),
             # Gets the date and time of the unit price and market
             # value. This is a required field according to the OFX
             # spec.
             ('marketValueDate', datetime, True, 'dtpriceasof'),
             # Gets the currency code of the position. This is an
             # optional field according to the OFX spec. If not
             # present, it's the default currency of the account.
             ('currencyCode', str, False, 'currency'),
             # Gets the memo associated with the position. This is an
             # optional field according to the OFX spec.
             ('memo', str, False, 'memo'),
             # Gets the 401K source for the sale. Should be one of
             # "PRETAX", "AFTERTAX", "MATCH", "PROFITSHARING",
             # "ROLLOVER", "OTHERVEST", "OTHERNONVEST". This is an
             # optional field according to the OFX spec.
             ('inv401kSource', str, False, 'inv401ksource'))


# posdebt
makeOfxClass('DebtPosition',
             ('investment', 'InvestmentPosition', True, 'invpos'))

# posmf
makeOfxClass('MutualFundPosition',
             ('investment', 'InvestmentPosition', True, 'invpos'),
             # Gets the number of units in the financial
             # insititution's street name.
             ('unitsStreet', Decimal, False, 'unitsstreet'),
             # Gets the number of units in the user's name.
             ('unitsUser', Decimal, False, 'unitsuser'),
             # Gets whether dividends are automatically reinvested.
             ('reinvestDividends', bool, False, 'reinvdiv'),
             # Gets whether capital gains are automatically reinvested. 
             ('reinvestCapitalGains', bool, False, 'reinvcg'))

# posopt
makeOfxClass('OptionsPosition',
             ('investment', 'InvestmentPosition', True, 'invpos'),
             # Gets how the options position is secured (for short
             # positions. One of: NAKED or COVERED
             ('secured', str, False, 'secured'))

# posother
makeOfxClass('OtherPosition',
             ('investment', 'InvestmentPosition', True, 'invpos'))

# posstock
makeOfxClass('StockPosition',
             ('investment', 'InvestmentPosition', True, 'invpos'),
             # Gets the number of units in the financial
             # insititution's street name.
             ('unitsStreet', Decimal, False, 'unitsstreet'),
             # Gets the number of units in the user's name.
             ('unitsUser', Decimal, False, 'unitsuser'),
             # Gets whether dividends are automatically reinvested.
             ('reinvestDividends', bool, False, 'reinvdiv'))

def parseInvestmentPosList(soup):
  if soup.name == 'posdebt':
    return DebtPosition(soup)
  elif soup.name == 'posmf':
    return MutualFundPosition(soup)
  elif soup.name == 'posother':
    return OtherPosition(soup)
  elif soup.name == 'posopt':
    return OptionsPosition(soup)
  elif soup.name == 'posstock':
    return StockPosition(soup)
  else: 
    print "Unknown type of position %s" % (soup.name)
    return None

def findAccountByNameList(root, namelist):
  """Find an account starting from root, namelist is a list of accounts
  to descend into like ('Assets', 'Investments', 'Citibank',
  'Checking') """
  if len(namelist) == 0:
    return root
  child=root.lookup_by_name(namelist.pop(0))
  if child.get_instance() is not None:
    return findAccountByNameList(child, namelist)

def findAccountByNameString(name_string):
  """Finds account based on name string starting from rootlike
  Assets:Investments:Something
  """
  return findAccountByNameList(session.book.get_root_account(),
                               name_string.split(':'))

def findAccountByNameOrDie(accountName):
  ret = findAccountByNameString(accountName)
  if ret is None:
    raise Exception("Unable to find '%s' account" % (accountName))
  return ret
    
###
### Global variables
### 
session = None
brokeragesRoot = None
brokerAccount = None
brokerSubAccounts = {}
securityIdToCommodityMap = {}
securityIdToAccountMap = {}
ofx = None

#
# Return or create sub-account NAME under the brokerAccount
#
# The names correspond to OFX file accountHeldIn field, which could be
# CASH, MARGIN, SHORT and OTHER
#
# We create only CASH initially, and other ones as needed when
# OFX file contains reference to them
# 
def getSubAccount(name):
  global brokerAccount, brokerSubAccounts
  name = name[0].upper() + name[1:].lower()
  if brokerSubAccounts.has_key(name):
    return brokerSubAccounts.get(name)
  else:
    type = ACCT_TYPE_BANK
    ret = findOrCreateBrokerAccount(brokerAccount, name, brokerAccount.GetCode(),
                                     brokerAccount.GetCommodity(),
                                     type, True)
    return ret


# iterator that gets all commodities in the table
def getAllCommodities():
  global session
  for ns in session.book.get_table().get_namespaces_list():
    for c in ns.get_commodity_list():
      yield c

# Return GnuCash commodity with specified UID (cusip). If can't find
# it the commodity, create it first
def findOrCreateCommodity(uid, uidtype, ns, ticker, name):
  global session

  comtab = session.book.get_table()
  c = comtab.lookup_unique(uidtype + "::" + uid)
  if c.get_instance() is not None:
      return c
  print 'Creating commodity(%s, %s, %s, %s, %s, %s)' % (session.book, type(name), ns, ticker, uid, 10000)
  c = GncCommodity(session.book, name.encode(), uidtype.encode(), uid.encode(), uid.encode(), 10000)
  c.set_quote_flag(True)
  c.set_quote_source(gnc_quote_source_lookup_by_internal("yahoo"))
  return comtab.insert(c)

# def checkCommodityForRename(uid, ticker):
#   global session

#   # print "Checking commodity %s for rename, ticker %s" % (uid, ticker)
#   comtab = session.book.get_table()

#   for c in getAllCommodities():
#     if c.get_cusip() == uid:
#       # print "Found same cusip, mnemonic=%s" % (c.get_mnemonic())
#       if ticker != c.get_mnemonic():
#         print "Commodity %s renamed to %s" % (c.get_mnemonic(), ticker)
#         c.old_mnemonic = c.get_mnemonic()
#         comtab.remove(c)
#         c.set_mnemonic(ticker)
#         comtab.insert(c)
#       return c
#   return None

def getSecListEntry(secId):
  """Return security description from SECLIST based on security id"""
  global ofx
  for sec in ofx.secList:
    if sec.securityInfo.securityId.uniqueIdType == secId.uniqueIdType \
       and sec.securityInfo.securityId.uniqueId == secId.uniqueId:
      return sec
  raise Exception("Security %s:%s not found in OFX SECLIST" % (
    secId.uniqueIdType, secId.uniqueId))

def getCommodityForSecId(secId):
  global securityIdToCommodityMap
  key = secId.uniqueIdType + ':' + secId.uniqueId
  if securityIdToCommodityMap.has_key(key):
    comm = securityIdToCommodityMap[key]
    return comm
  if auto_create_commodity_accounts:
    # find ticker in seclist
    security = getSecListEntry(secId)
    info = security.securityInfo
    comm = findOrCreateCommodity(secId.uniqueId, secId.uniqueIdType,
                                 security.commodityNamespace,
                                 info.ticker, info.securityName) 
    securityIdToCommodityMap[key] = comm
    # print "Created commodity %s => %s, %s" % (secId, comm.get_instance(),
    #                                           hasattr(comm, 'old_mnemonic'))
    return comm
  raise Exception('Unable to find commodity for securityId %s' % (secid))



def getAccountForSecId(secId):
  global session, brokerAccount, ofx, securityIdToAccountMap
  key = secId.uniqueIdType + ':' + secId.uniqueId
  if securityIdToAccountMap.has_key(key):
    return securityIdToAccountMap[key]
  
  poslist = ofx.stmtResponse.positions
  security = getSecListEntry(secId)
  info = security.securityInfo

  if isinstance(security, MutualFundSecurityInfo): secns = 'FUND'
  else: secns = 'AMEX'

  comm = getCommodityForSecId(secId)

  # print "comm cusip = %s mnemonic=%s secid=%s" % (comm.get_cusip(), comm.get_mnemonic(), secId)

  parent = brokerAccount
  prefix = ''

  if isinstance(security, MutualFundSecurityInfo):
    prefix = brokerage_account_mutual_funds
    acct_type = ACCT_TYPE_MUTUAL
  elif isinstance(security, DebtSecurityInfo):
    prefix = brokerage_account_bonds
    # ok not sure what to do here?
    acct_type = ACCT_TYPE_MUTUAL
  elif isinstance(security, OptionSecurityInfo):
    prefix = brokerage_account_options
    # ok not sure what to do here?
    acct_type = ACCT_TYPE_STOCK
  else:
    prefix = brokerage_account_stocks
    acct_type = ACCT_TYPE_STOCK

  if prefix != '':
    parent = parent.lookup_by_name(prefix)
    if parent.get_instance() is None:
      if auto_create_commodity_accounts:
        parent = findOrMakeAccount((prefix,),
                                      brokerAccount, session.book,
                                      brokerAccount.GetCommodity(),
                                      ACCT_TYPE_BANK)
        parent.SetPlaceholder(True)
      else:
        raise Exception('Account %s:%s not found' \
                      % (getAccountPath(brokerAccount), prefix))

  commAcc = parent.lookup_by_code(key)
  if commAcc.get_instance() is None:
    # print "Account by code %s not found, trying name %s" % (key, comm.get_mnemonic())
    commAcc = parent.lookup_by_name(comm.get_mnemonic())
    if commAcc.get_instance() is not None:
      # print "Found account by name, code %s commodity %s" % (commAcc.GetCode(),
      #                                                        commAcc.GetCommodity().get_cusip())
      # see if its different valid account with the correct commodity and code
      foundCusip  = commAcc.GetCommodity().get_cusip()
      if len(foundCusip) > 0 and commAcc.GetCode()[-len(foundCusip):] == foundCusip:
        # print "Ignoring account %s code %s" % (commAcc.GetName(), commAcc.GetCode())
        commAcc = Account(instance=None)


  if commAcc.get_instance() is None:
    if auto_create_commodity_accounts:
      commAcc = makeCommodityAccount(session.book, parent, comm, acct_type)
    else:
      raise Exception('Account for commodity %s does not exist under %s' \
                      % (comm.get_unique_name(), getAccountPath(parent)))
  
  if not gnc_commodity_equal(commAcc.GetCommodity().get_instance(), comm.get_instance()):
    raise Exception('Found account %s but its commodity %s is different then OFX file commodity %s' \
                    % (getAccountPath(commAcc),
                     commAcc.GetCommodity().get_unique_name(),
                     comm.get_unique_name()))
  if commAcc.GetCode() != key:
    if commAcc.GetCode() != '':
      print "Changing account code from %s to %s" % (commAcc.GetCode(), key)
    commAcc.SetCode(key)
  # Fix it up so that account has lots
  # splits = commAcc.GetSplitList()
  # if len(splits) > 0:
  #   last = splits[-1]
  #   last.GetParent().ScrubGains(gainsAccount)
  securityIdToAccountMap[key] = commAcc
  return commAcc

def getAccountPath(account):
  """ Return full name of account starting from root """
  if account.get_parent().get_instance() is None:
    return '' #  this is  root
  else:
    path = getAccountPath(account.get_parent())
    if path != '': return path + ':' + account.GetName()
    else: return account.GetName()

def findOrMakeAccount(account_tuple, root_account, book,
                         currency, acct_type ):
    current_account_name, account_path = account_tuple[0], account_tuple[1:]
    current_account = root_account.lookup_by_name(current_account_name)
    if current_account.get_instance() == None:
      current_account = Account(book)
      current_account.SetName(current_account_name)
      current_account.SetCommodity(currency)
      root_account.append_child(current_account)
    
    if len(account_path) > 0:
      return findOrMakeAccount(account_path, current_account, book,
                                    currency, acct_type)
    else:
      current_account.SetType(acct_type)
      account_commod = current_account.GetCommodity()
      if (account_commod.get_mnemonic(),
          account_commod.get_namespace() ) == \
          (currency.get_mnemonic(),
           currency.get_namespace()) :
        return current_account
      else:
        return None

def makeCommodityAccount(book, parent, comm, acct_type ):
  acc = Account(book)
  acc.SetName(comm.get_mnemonic())
  acc.SetCommodity(comm)
  acc.SetType(acct_type)
  parent.append_child(acc)
  return acc

def findOrCreateBrokerAccount(parent, name, acctId, currency, acctType, searchByName = False):
  global session
  if searchByName:
    ret = parent.lookup_by_name(name)
  else:
    ret = parent.lookup_by_code(acctId)
  if ret.get_instance() is not None:
    if ret.GetCommodity().get_unique_name() \
       != currency.get_unique_name():
      raise Exception('Found existing account %s (code %s) but account currency %s does not match OFX file currency %s' \
                      % (getAccountPath(ret),
                         ret.GetCode(),
                         ret.GetCommodity().get_unique_name(),
                         currency.get_unique_name()))
  elif auto_create_brokerage_accounts:
    # create account with same name as orgname
    ret = findOrMakeAccount((name,), parent, session.book, currency, acctType)
    # we search by this
    ret.SetCode(acctId)
  else:
    if searchByName:
      raise Exception('No account %s exists, please create an account named %s' % (
        name, getAccountPath(parent) + ":" + name))
    else:
      raise Exception('No account for with code %s exists under %s please create it' % (
        acctId, getAccountPath(parent)))
  return ret

# Find root broker account, this will be named
# same as generic name of the broker, ie amertrade.com or such
# under it we may have separate accounts for Cash
# and then stocks, bonds, market indexes
def findBrokerAndCashAccount():
  global session, brokerAccount, brokerSubAccounts, ofx
  orgName = ofx.signonResponse.orgName
  accFrom = ofx.stmtResponse.investmentAccountFrom
  acctId = accFrom.accountId
  curName = ofx.stmtResponse.currencyCode
  currency = session.book.get_table().lookup_unique('CURRENCY::' + curName)
  if currency.get_instance() is None:
    raise Exception('Unable to find OFX file currency %s in commodities table' % (curName))

  brokerAccount = findOrCreateBrokerAccount(brokeragesRoot, orgName, acctId, currency,
                                            ACCT_TYPE_BANK)
  
  cashAccount = getSubAccount("CASH")

  if auto_create_income_and_expanse_accounts:
    commissionsAccount = findOrMakeAccount(commissions_account.split(':'),
                                           session.book.get_root_account(),
                                           session.book,
                                           brokerAccount.GetCommodity(),
                                           ACCT_TYPE_EXPENSE)

    incomeRoot = findOrMakeAccount(income_account_root.split(':'),
                                   session.book.get_root_account(),
                                   session.book,
                                   brokerAccount.GetCommodity(),
                                   ACCT_TYPE_INCOME)

    taxExepmtRoot = findOrMakeAccount(income_account_tax_exempt_root.split(':'),
                                      session.book.get_root_account(),
                                      session.book,
                                      brokerAccount.GetCommodity(),
                                      ACCT_TYPE_INCOME)

    for incomeType in income_type_accounts:
      findOrMakeAccount((income_account_root + ':' + incomeType).split(':'),
                        session.book.get_root_account(),
                        session.book,
                        brokerAccount.GetCommodity(),
                        ACCT_TYPE_INCOME)
      findOrMakeAccount((income_account_tax_exempt_root
                         + ':' + incomeType).split(':'),
                        session.book.get_root_account(),
                        session.book,
                        brokerAccount.GetCommodity(),
                        ACCT_TYPE_INCOME)

def convertOfxDateTime(dt):
  dt = re.sub('(\.[0-9]*)?\[.*\]$', '', str(dt))
  if len(dt) == 14:
    divisor = 10000000000
  elif len(dt) == 12:
    divisor = 100000000
  elif len(dt) == 8:
    divisor = 10000
  else: raise Exception('Invalid datetime |%s|' % (dt))
  dt = int(dt)
  year = dt / divisor
  dt = dt % divisor
  divisor = divisor / 100
  month = dt / divisor
  dt = dt % divisor
  divisor = divisor / 100
  day = dt / divisor
  dt = dt % divisor
  divisor = divisor / 100
  if divisor > 0:
    hour = dt / divisor
    dt = dt % divisor
    divisor = divisor / 100
    minute = dt / divisor
    dt = dt % divisor
    divisor = divisor / 100
    if divisor > 0:
      second = dt / divisor
      dt = dt % divisor
      divisor = divisor / 100
    else: second = 0
  else:
    hour = 0
    minute = 0
    second = 0
  return datetime(year, month, day, hour, minute, second)

def datetime_to_unix(datetime):
  return long(time.mktime(datetime.timetuple()))


def createPositionAdjustments(adjust_positions):
  """ Adjust balances in commodity accounts so they would agree with OFX file POSLIST
  This should only be happenning on initial import, where the OFX file does not contain
  buy/sell transactions for the securities in POSLIST, or if some buy/sell transactions
  are missing form the OFX file

  if ADJUST_POSITOINS is passed, then do it, otherwise give a warning """

  global session, brokerAccount, ofx
  poslist = ofx.stmtResponse.positions

  didWarn = False

  # Interactive brokers sends separate <posstock> entry for each lot. so its possible
  # to have multiple entlies for same security
  # sum entries for the same security first, then compare
  
  ofxBalances = {};

  print "\n\n Scanning for balance mistmatches \n\n"


  for pos in poslist:
    investment = pos.investment
    secId = investment.securityId
    date = investment.marketValueDate

    commAcc = getAccountForSecId(secId)
    ofxBal = investment.units

    # we keep number of option shares as *100 in gnucash, so total value is correct
    if isinstance(pos, OptionsPosition):
      ofxBal *= 100

    key = secId.uniqueIdType + ':' + secId.uniqueId
    if (not ofxBalances.has_key(key)):
      ofxBalances[key] = {
        'bal': Decimal('0.0'),
        'secId': secId,
        'date': date,
        'price': investment.unitPrice
      };
    ofxBalances[key]['bal'] += ofxBal

  for pos in ofxBalances.values():
    secId = pos['secId']
    date = pos['date']
    ofxBal = pos['bal']
    price = pos['price']

    commAcc = getAccountForSecId(secId)

    bal = gnc_numeric_to_python_Decimal(commAcc.GetBalance())
    otherAccount = None

    if bal != ofxBal:
      didWarn = True
      print '%s OFX balance=%s our balance=%s (net %s)' % (
        getAccountPath(commAcc), ofxBal, bal, ofxBal - bal)
      if not adjust_positions:
        continue
      # adjust it
      otherAccount = findAccountByNameOrDie('Equity:Opening Balances')
      desc = 'Adjustment from OFX file position'

      make_transaction(
        commAcc, otherAccount, ofxBal - bal, price, date, desc)
  if didWarn and not adjust_positions:
    print "\n\nThere is a mistmatch between position sizes in OFX file and GnuCash."
    print "This is normal if trades were performed only a few days ago, sometimes"
    print "there is a delay of 3-5 days before trades settle and show up in OFX file"
    print ""
    print "If these positions were bought long time ago, or its the first time you are"
    print "importing them into GnuCash, please run this script with -b option"
    print "to create adjustments that will record the initial amount of shares you have"

def updateCommodityPrices():
  """Update the commodities price table with prices from OFX file
  POSLIST. The quote source is set to OFX file ORG element, which is
  usually broker name like ameritrade.com """
  global session, brokerAccount, ofx

  poslist = ofx.stmtResponse.positions

  for pos in poslist:
    investment = pos.investment
    secId = investment.securityId
    date = investment.marketValueDate

    commAcc = getAccountForSecId(secId)

    pdb = session.book.get_price_db()

    prices = pdb.get_prices(commAcc.GetCommodity(),
                            brokerAccount.GetCommodity())
    day = date.date()
    code = ofx.signonResponse.orgName

    # first try to find our quote on this day, in case it already exist
    prices = [p for p in prices if p.get_time() == day
              and p.get_source() == code]
    if len(prices) > 0:
      # should not be more then one really. Well actually user can
      # probably insert a duplicate manually, unless gnucash enforces it
      for p in prices:
        p.set_value(gnc_numeric_from_decimal(investment.unitPrice).get_instance())
    else:
      p = GncPrice(instance=gnc_price_create(session.book.get_instance()))
      p.set_time(day)
      p.set_commodity(commAcc.GetCommodity())
      p.set_currency(brokerAccount.GetCommodity())
      p.set_value(gnc_numeric_from_decimal(investment.unitPrice).get_instance())
      p.set_typestr('last')
      p.set_source(code)
      pdb.add_price(p)

def make_transaction(commAcc, otherAccount, shares, price, date, desc, taxExempt = False,
                     transId = None,
                     scrabGains = True):
  """Create two ends of a stock or mutual fund transaction. otherAccount
  must be a bank or other cash account.. otherAccount can be None then
  transaction will be unbalanced.

  Parameters:

  commAcc, otherAccount -> GnuCash accounts
  shares, price         -> Python Decimal objects
  date                  -> Python datetime
  desc                  -> description

  """
  global session, brokerAccount

  tran = Transaction(session.book)
  tran.BeginEdit()
  tran.SetCurrency(brokerAccount.GetCommodity())
  tran.SetDescription(desc)

  tran.SetDatePostedSecs(datetime_to_unix(date))
  if transId is not None:
    tran.SetNotes(transId)

  s1 = Split(session.book)
  s1.SetParent(tran)
  s1.SetAccount(commAcc)
  s1.SetSharePriceAndAmount(gnc_numeric_from_decimal(price),
                            gnc_numeric_from_decimal(shares))

  # create opposite end of the transaction (where money comes from)
  if otherAccount is not None:
    s2 = Split(session.book)
    s2.SetParent(tran)
    s2.SetAccount(otherAccount)
    s2.SetValue(s1.GetValue().neg())

  tran.CommitEdit()

  if scrabGains:
    print "Scrubbing gains"
    gainsAccount = findAccountByNameOrDie(getIncomeAccountName("CGSHORT", taxExempt))
    # tran = s1.GetParent()
    tran.BeginEdit()
    tran.ScrubGains(None)
    tran.CommitEdit()
    splits = commAcc.GetSplitList()
    for s in splits:
      other = s.GetOtherSplit()
      print "Processing split=%s other=%s" % (s, other)
      if other.get_instance() is None:
        continue
      acc = other.GetAccount()
      print "Split %s" % (getAccountPath(acc))

      if acc.GetName().find('Orphaned Gains-') == 0:
        v1 = s.GetValue()
        v2 = other.GetValue()

        oldTran = s.GetParent()

        tran.BeginEdit()
        oldTran.BeginEdit()

        s.SetParent(tran)
        other.SetParent(tran)

        other.SetAccount(gainsAccount)

        tran.CommitEdit()
        oldTran.CommitEdit()


def make_transaction2(firstAcc, otherAccount, tranType, amount, date, desc, transId = None):
  """Create two ends of a regular (not stock or mutual fund) account
  transaction.

  By default the transaction being setup is the transfer of money from
  otherAccount into firstAccount, ie a credit transaction. if TRANTYPE is
  DEBIT, then we reverse the sign

  Parameters:

  firstAccount, otherAccount -> GnuCash accounts. otherAccount can be None
  tranType                   -> either DEBIT or CREDIT.
  amount                -> python decimal
  date                  -> Python datetime
  desc                  -> description

  """
  global session, brokerAccount

  tran = Transaction(session.book)
  tran.BeginEdit()
  tran.SetCurrency(brokerAccount.GetCommodity())
  tran.SetDescription(desc)
  if transId is not None:
    tran.SetNotes(transId)

  tran.SetDatePostedSecs(datetime_to_unix(date))

  s1 = Split(session.book)
  s1.SetParent(tran)
  s1.SetAccount(firstAcc)

  # ok at least for ameritrade, it seems when tranType is DEBIT
  # the amount is already reversed in the OFX file
  #if tranType == 'DEBIT': amount = -amount
  s1.SetValue(gnc_numeric_from_decimal(amount));

  # create opposite end of the transaction (where money comes from)
  if otherAccount is not None:
    s2 = Split(session.book)
    s2.SetParent(tran)
    s2.SetAccount(otherAccount)
    s2.SetValue(s1.GetValue().neg())

  tran.CommitEdit()
  return s1

def getIncomeAccountName(incomeType, taxExempt):
  "Return full GnuCash account name for where income should go."
  name = income_account_root
  if taxExempt: income = income_account_tax_exempt_root
  name += ':'
  if incomeType == 'CGLONG': name += income_type_accounts[0]
  elif incomeType == 'CGSHORT': name += income_type_accounts[1]
  elif incomeType == 'DIV': name += income_type_accounts[2]
  elif incomeType == 'INTEREST': name += income_type_accounts[3]
  elif incomeType == 'MISC': name += income_type_accounts[4]
  elif incomeType == 'FUTURE': name += income_type_accounts[5]
  else:
    print "Warning: unknown OFX income type %s" % (incomeType)
    name += income_type_accounts[4]
  return name

def findIfDuplicate(account, date, amount, memo, transId):
  """Find a duplicate transaction. If amount is a tuple, then its
  (shares, sharePrice) """
  units, unitPrice = (None, None)
  if isinstance(amount, tuple):
    units, unitPrice = amount
    unitPrice = unitPrice.quantize(Decimal('1.00'))
    amount = None
  else:
    amount = amount.quantize(Decimal('1.00'))

  for split in account.GetSplitList():
    trans = split.parent

    transDate = date.fromtimestamp(trans.GetDate())
    transAmount = gnc_numeric_to_python_Decimal(split.GetValue()).quantize(Decimal('1.00'))
    transNote = trans.GetNotes()
    transMemo = trans.GetDescription()

    # definitely a dup, because we store transId in user-invisible note
    # note that we match this before matching Units
    #
    # This is because the cap gains code can split teh actual transaciton into
    # multiples, in order to match buy/sell lots
    #
    # For example if we bought 100 shares, then 200, then imported sell for 300, the
    # 300 shares sell will be split into selling 100 and 200, in order to match
    # the lots that we bought.
    #
    # Next time we try to re-import same sell 300 shares transation, a
    # naive search for duplicate would search for 300 shares sold at
    # same price on same day, which we won't find. So rely on
    # transaction ID's being unique instead, and catch duplicate based
    # on that. If there are transacitons with same transaction ids,
    # then we are screwed
    if transId is not None and transId != "" \
       and transNote == transId:
      return True

    if amount is not None:
      if amount != transAmount:
        continue
    else:
      transUnits = gnc_numeric_to_python_Decimal(split.GetAmount())
      transUnitPrice = gnc_numeric_to_python_Decimal(split.GetSharePrice()).quantize(Decimal('1.00'))

      # print "Here units=%s unitPrice=%s transUnits=%s transUnitPrice=%s" % (units, unitPrice,
      #                                                                      transUnits, transUnitPrice)
      if units != transUnits or unitPrice != transUnitPrice:
        # print 'Units or price dont match'
        continue

    daysApart = abs((transDate - date).days)
    if daysApart > 5:
      # print 'More then 5 days apart'
      continue


    # print "Here transId = %s transNote=%s" % (transId, transNote)
    # definitely not a dup, because we store transId in user-invisible note
    if transId is not None and transId != "" and transNote is not None \
       and transNote != "" and transNote != transId:
      # print 'Definitely not a dup'
      continue

    # If memo is non empty and equal, and less then 3 days apart, then a dup
    if daysApart <= 5 and memo is not None and memo == transMemo:
      return True

    # ok memo is different, in this case only a dup if its withing 2 days
    if daysApart <= 2:
      return True
  return False

def handleRenamedCommodities():
  """Ensure that we have every commodity and account, this handles renames as well"""
  global ofx
  for sec in ofx.secList:
    secId = sec.securityInfo.securityId
    comm = checkCommodityForRename(secId.uniqueId, sec.securityInfo.ticker)
    if comm is not None:
      global securityIdToCommodityMap
      key = secId.uniqueIdType + ':' + secId.uniqueId
      securityIdToCommodityMap[key] = comm
      # print "Changed hash on renamed commodity %s => %s, %s" % (secId, comm.get_instance(),
      #                                                           hasattr(comm, 'old_mnemonic'))
  for sec in ofx.secList:
    secId = sec.securityInfo.securityId
    comm = getCommodityForSecId(secId)
    acc = getAccountForSecId(secId)

def isOppositeTransferTransaction(acc1, tran1, tran2):
  if not isinstance(tran1, TransferTransaction) \
     or not isinstance(tran2, TransferTransaction): return False

  if tran1.units != -tran2.units:
    # print "here0 tran1.units=%s tran2.units=%s" % (tran1.units, tran2.units)
    return False

  if tran1.unitPrice != tran2.unitPrice:
    # print "here2"
    return False

  if tran1.invTran.tradeDate != tran2.invTran.tradeDate:
    # print "here3"
    return False

  if tran1.subAccountSec != tran2.subAccountSec:
    # print "here4"
    return False

  if tran1.type != tran2.type:
    # print "here44"
    return False

  if (tran1.transferAction == "OUT" and tran2.transferAction != "IN"):
    # print "here5"
    return False

  if (tran1.transferAction == "IN" and tran2.transferAction != "OUT"):
    # print "here6"
    return False
  

  secId1 = tran1.securityId
  secId2 = tran2.securityId

  comm1 = acc1.GetCommodity()
  comm2 = getCommodityForSecId(secId2)

  mnem1 = comm1.old_mnemonic if hasattr(comm1, 'old_mnemonic') else comm1.get_mnemonic()
  mnem2 = comm2.old_mnemonic if hasattr(comm2, 'old_mnemonic') else comm2.get_mnemonic()

  cusip1 = comm1.get_cusip()
  cusip2 = comm2.get_cusip()

  # ok if either ticker or cusip is unchanged, then consider it a rename
  if mnem1 != mnem2 and cusip1 != cusip2:
    # print "Here7 mnem1=%s mnem2=%s cusip1=%s cusip2=%s" % (mnem1,
    #                                                        mnem2,
    #                                                        cusip1, cusip2)
    return False

  acc2 = getAccountForSecId(secId2)

  bal1 = abs(gnc_numeric_to_python_Decimal(acc1.GetBalance())) 
  bal2 = abs(gnc_numeric_to_python_Decimal(acc2.GetBalance())) 

  if (bal1 == 0 and abs(bal2) == abs(tran1.units)) \
     or (bal2 == 0 and abs(bal1) == abs(tran1.units)):
    # print "Here8 returning True"
    return True
  else:
    # print "here9 bal1 = %s tran1.units = %s bal2 = %s " \
    # % (bal1, tran1.units, bal2)
    return False

def updateTransactionList():
  """Copy the banking and investment transactions from OFX file """
  global session, brokerAccount, ofx
  matched = []
  for tran in ofx.stmtResponse.transactions.bankTransactions:
    if tran in matched:
      continue
    acc1Type = tran.subAccountFund  # CASH, MARGIN etc
    acc1 = getSubAccount(acc1Type)  
    tranType = tran.transaction.type
    timePosted = tran.transaction.timePosted
    amount = tran.transaction.amount
    memo = tran.transaction.memo
    transId = tran.transaction.transactionId

    # Lets see if its a duplicate
    if findIfDuplicate(acc1, timePosted, amount, memo, transId):
      #print "Found suspected duplicate %s:%s skipping" % (tran.subAccountFund, tran.transaction)
      continue

    # We don't have access to GUI here, so we can't popup GnuCash "find matching accoun"
    # dialog.. But a lot of brokereges have a matching pair of transactions daily between
    # CASH and MARGIN accounts
    #
    # Try to find the transaction with either same amount and opposite
    # TRANTYPE (ie 10k debit from MARGIN is matched with 10k credit
    # into CASH) or a transaciton with same type, but opposite sign
    # amounts, ie -10k credit to MARGIN and 10k credit to CASH)
    #
    # Otherwise transaction will remain unbalanced, and user will have
    # to balance it manually
    #
    acc2 = None
    tran2list = [tran2 for tran2 in ofx.stmtResponse.transactions.bankTransactions
                if tran2 != tran and tran2.subAccountFund != tran.subAccountFund
                and (tran2.transaction.amount == -amount and tran2.transaction.type != tranType)]
    if len(tran2list) == 1:
      print "Found match %s:%s for %s:%s" % (
        tran.subAccountFund, tran.transaction,
        tran2list[0].subAccountFund, tran2list[0].transaction)
      acc2 = getSubAccount(tran2list[0].subAccountFund)
      matched.append(tran2list[0])
    make_transaction2(acc1, acc2, tranType, amount, timePosted, memo, transId)

  #
  # Now update investment transactions
  #

  for tran in ofx.stmtResponse.transactions.investmentTransactions:
    if tran in matched:
      continue
    invTran = None
    subAccount = 'CASH'
    otherAccountName = None
    otherAccount = None
    amount = None
    secId = None
    taxExempt = None
    inv401kSource = None

    if isinstance(tran, MarginInterestTransaction) or isinstance(tran, IncomeTransaction) \
       or isinstance(tran, ExpenseTransaction):
      invTran = tran.invTran
      subAccount = tran.subAccountFund or tran.subAccountSec or 'CASH'
      amount = tran.total
      if isinstance(tran, MarginInterestTransaction):
        # otherAccountName = commissions_account
        otherAccType = 'MISC'
      else:
        secId = tran.securityId
        if isinstance(tran, IncomeTransaction):
          taxExempt = tran.taxExempt
          otherAccType = tran.incomeType
        else: # its expense
          taxExempt = False
          otherAccType = 'MISC'
      memo = invTran.memo
      if memo.find('FUTURE') == 0:
        otherAccType = 'FUTURE'
      otherAccountName = getIncomeAccountName(otherAccType, taxExempt)
      transId = invTran.transactionId
      tradeDate = invTran.tradeDate
      subAccount = getSubAccount(subAccount)

      # Lets see if its a duplicate
      if findIfDuplicate(subAccount, tradeDate, amount, memo, transId):
        #print "Found suspected duplicate %s skipping" % (tran)
        continue

      print "NEW transaction %s" % (tran)
      make_transaction2(subAccount,
                        findAccountByNameOrDie(otherAccountName), 
                        'CREDIT',
                        amount,
                        tradeDate, memo, transId)
    elif isinstance(tran, BuyMFTransaction) \
    or isinstance(tran, SellMFTransaction) \
    or isinstance(tran, BuyOptionTransaction) \
    or isinstance(tran, SellOptionTransaction) \
    or isinstance(tran, BuyStockTransaction) \
    or isinstance(tran, SellStockTransaction) \
    or isinstance(tran, BuyDebtTransaction) \
    or isinstance(tran, SellDebtTransaction) \
    or isinstance(tran, BuyOtherTransaction) \
    or isinstance(tran, SellOtherTransaction):
      tranType = ''
      if isinstance(tran, BuyMFTransaction) \
         or isinstance(tran, SellMFTransaction) \
         or isinstance(tran, BuyOptionTransaction) \
         or isinstance(tran, SellOptionTransaction) \
         or isinstance(tran, BuyStockTransaction) \
         or isinstance(tran, SellStockTransaction):
        tranType = tran.type
        if tranType is None or tranType == '':
          if isinstance(tran, BuyMFTransaction): tranType = 'Buy Mutual Fund'
          elif isinstance(tran, BuyOptionTransaction): tranType = 'Buy Option'
          elif isinstance(tran, BuyStockTransaction):  tranType = 'Buy Stock'
          elif isinstance(tran, SellMFTransaction): tranType = 'Sell Mutual Fund'
          elif isinstance(tran, SellOptionTransaction): tranType = 'Sell Option'
          elif isinstance(tran, SellStockTransaction):  tranType = 'Sell Stock'
      investment = tran.investment
      invTran = investment.invTran
      transId = invTran.transactionId
      secId = investment.securityId
      units = investment.units
      unitPrice = investment.unitPrice
      commission = investment.commission or Decimal('0.0')
      fees = investment.fees or Decimal('0.0')
      total = investment.total
      taxExempt = investment.taxExempt
      subAccount = investment.subAccountFund or investment.subAccountSec or 'CASH'
      memo = invTran.memo
      tradeDate = invTran.tradeDate
      commAcc = getAccountForSecId(secId)
      comm = getCommodityForSecId(secId)

      # if memo line is empty, make a memory line
      if memo is None or memo == '':
        memo = tranType
        if memo != '': memo += ' '
        memo += comm.get_mnemonic()
      elif tranType != '' and memo.lower().find('buy') == -1 \
           and memo.lower().find('sell') == -1 \
           and memo.lower().find('cover') == -1 \
           and memo.lower().find('short') == -1:
        memo = tranType + ' ' + memo

      #print "Processing investment transaction %s" % (transId)

      # Unfortunately there is no way to specify trade fraction
      # multiplier greater then one commodities, it would have been
      # cooler to have option's commodity have min trade fraction of 100/1
      #
      # Instead in GnuCash we count option contrans in number of
      # shares that they buy, rather then in contracts themself
      if isinstance(tran, BuyOptionTransaction) or isinstance(tran, SellOptionTransaction):
        units *= tran.sharesPerContract

      # Lets see if its a duplicate
      if findIfDuplicate(commAcc, tradeDate, (units, unitPrice), memo, transId):
        #print "Found suspected duplicate %s %s skipping" % (tran.__class__.__name__, tran.investment)
        continue

      print "NEW investment transaction %s" % (tran)
      make_transaction(
        commAcc, getSubAccount(subAccount),
        units, unitPrice,
        tradeDate, memo, taxExempt, transId,
        commissions = commissions + fees,
        commissionsAccount = findAccountByNameOrDie(commissions_account))
    elif isinstance(tran, TransferTransaction):
      invTran = tran.invTran
      investment = tran
      secId = investment.securityId
      units = investment.units
      unitPrice = investment.unitPrice or Decimal('0.0')
      tranType = 'Transfer ' + tran.transferAction

      transId = invTran.transactionId
      subAccount = investment.subAccountSec or 'CASH'
      memo = invTran.memo
      tradeDate = invTran.tradeDate
      sec = getSecListEntry(secId)
      commAcc = getAccountForSecId(secId)
      comm = getCommodityForSecId(secId)

      # if memo line is empty, make a memory line
      if memo is None or memo == '':
        memo = tranType
        if memo != '': memo += ' '
        memo += comm.get_mnemonic()
      elif tranType != '' and memo.lower().find('buy') == -1 \
           and memo.lower().find('sell') == -1 \
           and memo.lower().find('cover') == -1 \
           and memo.lower().find('assign') == -1 \
           and memo.lower().find('short') == -1:
        memo = tranType + ' ' + memo

      print "Processing transfer transaction %s secid=%s comm_unique_name=%s" \
        % (transId, secId, comm.get_unique_name())

      # Unfortunately there is no way to specify trade fraction
      # multiplier greater then one commodities, it would have been
      # cooler to have option's commodity have min trade fraction of 100/1
      #
      # Instead in GnuCash we count option contrans in number of
      # shares that they buy, rather then in contracts themself

      doScrab = False

      if isinstance(sec, OptionSecurityInfo):
        units *= sec.sharesPerContract
        doScrab = True

      # Lets see if its a duplicate
      if findIfDuplicate(commAcc, tradeDate, (units, unitPrice), memo, transId):
        print "Found suspected duplicate %s %s skipping" % (tran.__class__.__name__, tran)
        continue

      acc2 = None
      tran2list = [tran2 for tran2 in ofx.stmtResponse.transactions.investmentTransactions
                   if tran2 != tran and isOppositeTransferTransaction(commAcc, tran, tran2) ]
                     
      tran2 = None

      # print "Here tran2list = %s" % (len(tran2list))
      if len(tran2list) == 1:
        tran2 = tran2list[0]

      if tran2 is not None:
        if tran.transferAction == "OUT":
          print "Skipping OUT transaction %s for internal transfer" % (tran)
          continue

        # print "Found internal transfer match, will copy splits %s" % (tran2)
        acc1 = commAcc
        acc2 = getAccountForSecId(tran2.securityId)

        # Lets see if its a duplicate
        if findIfDuplicate(acc2, tradeDate, (Decimal('0'), Decimal('0')), memo, transId):
          print "Found suspected duplicate %s %s skipping" % (tran.__class__.__name__, tran)
          continue

        comm1 = acc1.GetCommodity()
        comm2 = acc2.GetCommodity()

        bal1 = gnc_numeric_to_python_Decimal(acc1.GetBalance()) 
        bal2 = gnc_numeric_to_python_Decimal(acc2.GetBalance())

        print "Here bal1=%s bal2=%s tran.units=%s" % (bal1, bal2, tran.units)
        assert tran.transferAction == "IN"
        assert bal1 == 0
        assert bal2 == tran.units

        # now rename the accounts
        key1 = secId.uniqueIdType + ':' + secId.uniqueId
        key2 = tran2.securityId.uniqueIdType + ':' + tran2.securityId.uniqueId
        
        acc2.SetCommodity(comm1)
        acc2.SetCode(key1)
        acc1.SetCommodity(comm2)
        acc1.SetCode(key2)

        global securityIdToAccountMap

        securityIdToAccountMap[key1] = acc2
        securityIdToAccountMap[key2] = acc1

        print "NEW internal transfer transaction %s" % (tran)
        make_transaction(
          commAcc, getSubAccount(subAccount),
          Decimal('0'), Decimal('0'),
          tradeDate, memo, taxExempt, transId,
          scrabGains = False )

      else:
        print "NEW transfer transaction %s doScrab=%s" % (tran, doScrab)
        make_transaction(
          commAcc, getSubAccount(subAccount),
          units, unitPrice,
          tradeDate, memo, taxExempt, transId,
          scrabGains = doScrab )


def doMain(gnuCashFileName, ofxFileName, dontSave, adjust_positions):
  global session, brokeragesRoot, brokerAccount, soup, ofx

  soup = BeautifulSoup(open(ofxFileName))
  url = "xml://"+gnuCashFileName
  session = Session(url, True, False, False)
  
  brokeragesRoot = findAccountByNameOrDie(brokerage_account_root)

  ofx = Ofx(soup);

  findBrokerAndCashAccount()
  #handleRenamedCommodities()
  updateTransactionList()
  # Now do final adjustments to balances as per OFX file
  createPositionAdjustments(adjust_positions)
  if auto_create_prices:
    updateCommodityPrices()
  if not dontSave: session.save()
  else: print "Gnucash file was not saved (dry run)"


dbg_gcfile='/home/max/Documents/Finances/test2.gnucash'
dbg_ofxfile='/home/max/Documents/Finances/viv.ofx'


def main():
  parser = argparse.ArgumentParser(description="Import Ameritrade OFX file into Gnu Cash")
  parser.add_argument('gnuCashFile', metavar='<gnucash file>')
  parser.add_argument('ofxFile', metavar='<ofx file>')
  parser.add_argument('-n', dest='dontSave', action='store_true', help='Dry run (do not save the file)')
  parser.add_argument('-b', dest='adjustBalances', action='store_true', help='Create initial balances (when trades are missing or for initial import)')
  args = parser.parse_args()
  doMain(args.gnuCashFile, args.ofxFile, args.dontSave, args.adjustBalances)

def dbg_main(gcfile=dbg_gcfile, ofxFile=dbg_ofxfile):
  doMain(dbg_gcfile, dbg_ofxfile, True, False)

if (os.getenv('INSIDE_EMACS') is None):
  main()
