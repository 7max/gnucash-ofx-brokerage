#!/usr/bin/python
import time, os, httplib, urllib2
import sys
import argparse
import calendar
from datetime import datetime

join = str.join

sites = {
       "ucard": {
                 "caps": [ "SIGNON", "CCSTMT" ],
                  "fid": "24909",
                "fiorg": "Citigroup",
                  "url": "https://secureofx2.bankhost.com/citi/cgi-forte/ofx_rt?servicename=ofx_rt&pagename=ofx",
                },
    "discover": {
                 "caps": [ "SIGNON", "CCSTMT" ],
                "fiorg": "Discover Financial Services",
                  "fid": "7101",
                  "url": "https://ofx.discovercard.com/",
                },
     "ameritrade": {
                 "caps": [ "SIGNON", "INVSTMT" ],
                "fiorg": "ameritrade.com",
                  "url":
                     #"https://ofx.ameritrade.com/ofxproxy/ofx_proxy.dll",
                 'https://ofxs.ameritrade.com/cgi-bin/apps/OFX',

                } 
    }

def _field(tag,value):
    return "<"+tag+">"+value

def _tag(tag,*contents):
    return join("\r\n",["<"+tag+">"]+list(contents)+["</"+tag+">"])

def _date():
    return time.strftime("%Y%m%d%H%M%S",time.localtime())

def _genuuid():
    return os.popen("uuidgen").read().rstrip().upper()

class OFXClient:
    """Encapsulate an ofx client, config is a dict containg configuration"""
    def __init__(self, config, user, password):
        self.password = password
        self.user = user
        self.config = config
        self.cookie = 3
        config["user"] = user
        config["password"] = password
        if not config.has_key("appid"):
            config["appid"] = "PyOFX"
            config["appver"] = "0100"

    def _cookie(self):
        self.cookie += 1
        return str(self.cookie)

    """Generate signon message"""
    def _signOn(self):
        config = self.config
        fidata = [ _field("ORG",config["fiorg"]) ]
        if config.has_key("fid"):
            fidata += [ _field("FID",config["fid"]) ]
        return _tag("SIGNONMSGSRQV1",
                    _tag("SONRQ",
                         _field("DTCLIENT",_date()),
                         _field("USERID",config["user"]),
                         _field("USERPASS",config["password"]),
                         _field("LANGUAGE","ENG"),
                         _tag("FI", *fidata),
                         _field("APPID",config["appid"]),
                         _field("APPVER",config["appver"]),
                         ))

    def _acctreq(self, dtstart):
        req = _tag("ACCTINFORQ",_field("DTACCTUP",dtstart))
        return self._message("SIGNUP","ACCTINFO",req)

    def _ccreq(self, acctid, dtstart):
        config=self.config
        req = _tag("CCSTMTRQ",
                   _tag("CCACCTFROM",_field("ACCTID",acctid)),
                   _tag("INCTRAN",
                        _field("DTSTART",dtstart),
                        _field("INCLUDE","Y")))
        return self._message("CREDITCARD","CCSTMT",req)

    def _invstreq(self, brokerid, acctid, dtstart, dtend):
        req = _tag("INVSTMTRQ",
                   _tag("INVACCTFROM",
                      _field("BROKERID", brokerid),
                      _field("ACCTID",acctid)),
                   _tag("INCTRAN",
                        _field("DTSTART",dtstart),
                        _field("DTEND",dtend),
                        _field("INCLUDE","Y")),
                   _field("INCOO","Y"),
                   _tag("INCPOS",
                        _field("DTASOF", dtend),
                        _field("INCLUDE","Y")),
                   _field("INCBAL","Y"))
        return self._message("INVSTMT","INVSTMT",req)

    def _message(self,msgType,trnType,request):
        config = self.config
        return _tag(msgType+"MSGSRQV1",
                    _tag(trnType+"TRNRQ",
                         _field("TRNUID",_genuuid()),
                         _field("CLTCOOKIE",self._cookie()),
                         request))
    
    def _header(self):
        return join("\r\n",[ "OFXHEADER:100",
                           "DATA:OFXSGML",
                           "VERSION:102",
                           "SECURITY:NONE",
                           "ENCODING:USASCII",
                           "CHARSET:1252",
                           "COMPRESSION:NONE",
                           "OLDFILEUID:NONE",
                           "NEWFILEUID:"+_genuuid(),
                           ""])

    def ccQuery(self, acctid, dtstart):
        """CC Statement request"""
        return join("\r\n",[self._header(),
                          _tag("OFX",
                               self._signOn(),
                               self._ccreq(acctid, dtstart))])

    def acctQuery(self,dtstart):
        return join("\r\n",[self._header(),
                          _tag("OFX",
                               self._signOn(),
                               self._acctreq(dtstart))])

    def invstQuery(self, brokerid, acctid, dtstart, dtend):
        return join("\r\n",[self._header(),
                          _tag("OFX",
                               self._signOn(),
                               self._invstreq(brokerid, acctid,dtstart,dtend))])

    def doQuery(self,query,name):
        # N.B. urllib doesn't honor user Content-type, use urllib2
        request = urllib2.Request(self.config["url"],
                                  query,
                                  { "Content-type": "application/x-ofx",
                                    "Accept": "*/*, application/x-ofx"
                                  })
        if 1:
            f = urllib2.urlopen(request)
            response = f.read()
            f.close()
            
            f = file(name,"w")
            f.write(response)
            f.close()
	else:
            print request
            print self.config["url"], query
        
        # ...

import getpass
if __name__=="__main__":

    parser = argparse.ArgumentParser(description="Download OFX file from an institution")
    parser.add_argument('site', metavar='site', help='One of ameritrade, ucard or discover')
    parser.add_argument('username', metavar='<username>')
    parser.add_argument('account', nargs='?', metavar='<account>')
    parser.add_argument('-d', dest='ndays', type=int, default=31, help='Number of days to download')
    parser.add_argument('-m', dest='month', type=int, help='month')
    args = parser.parse_args()

    if args.month is not None:
      dtstart = datetime.now().replace( month = args.month, day = 1)
      dtend = dtstart.replace(day = calendar.monthrange(dtstart.year, dtstart.month)[1])
      dtstart = dtstart.strftime("%Y%m%d")
      dtend = dtend.strftime("%Y%m%d")
    else:
      dtstart = time.strftime("%Y%m%d",time.localtime(time.time()-args.ndays*86400))
      dtend = time.strftime("%Y%m%d",time.localtime())
    # print "dtstart=%s dtend=%s" % (dtstart, dtend)
    passwd = getpass.getpass()
    client = OFXClient(sites[args.site], args.username, passwd)
    if args.account is None:
       query = client.acctQuery("19700101000000")
       client.doQuery(query, args.site+"_acct.ofx") 
    else:
       if "CCSTMT" in sites[args.site]["caps"]:
          query = client.ccQuery(args.account, dtstart)
       elif "INVSTMT" in sites[args.site]["caps"]:
          query = client.invstQuery(sites[args.site]["fiorg"], args.account, dtstart, dtend)
       client.doQuery(query, args.site+dtend+".ofx")

