#############################################################################
#
#  GPRTools.py
#  Interface to GoldenPR
#  Ido Carmi
#
#  Check main file -GoldenPR- for current version
#
#------------------------------------------------------
#
#  History:
#  Aug-20-2004 ido Changed golden rules to be case insensitive.
#  Nov-03-2004 ido First Production Instance (V.1.0.0)
#  Jan-05-2005 ido Changed to incoporate DCOracle2, new error message
#                  format, Python 2.3.4
#  Dec-13-2005 jn Modified fXMLParse to handle ManualCreate action
#  Mar-15-2006 jn Cosmetic changes to make code easier to digest,
#                 esp. added much needed comments
#  Mar-17-2006 jn Mods made to accommodate term information
#  Aug-31-2006 jn Mods to disable intra-SOR merges (which were made
#                 Aug10th) merged into code with term changes
#  Sep-21-2006 jn Add query functions for SIS & iVIP (change Util
#                 class to pass oLog/oProf at init) Add VIP
#                 integration
#  Apr-25-2007 jn Special handling for XML format for GDS Read for
#                 Course Role
#  May-02-2007 jn Use external module (GPRUtils.Hooks) to bypass
#                 request validation
#  Jun-07-2007 jn Change above to instead bypass bad data
#  Jul-09-2007 jn Send only previous/current/next-term course roles
#                 for Read ops
#                 Also get rid of unnecessary __del__'s
#  Sep-15-2010 rb Update DTM of record shell only if no data changed
#                 during an Update action.
#  Dec-01-2011 rb Made transactions to occur upon a Read more generic.
#
#------------------------------------------------------
#
#  Todo:
#    new list:
#      + Exceptions to the rule, e.g. accept AIS messed up names
#      + Possible bug: for multi-valued attributes, no exception raised
#        on invalid attribute in XML
#    old list:
#      + Make CreateRecordShell more generic
#      + Fix return object that contains updated attributes for data
#        propagation
#      + Groups:
#        + Implement sub-groups
#        + Implement special 'MAIN' "class-level" group
#
#############################################################################


"""
_____________________________________________________________________________
_____________________________________________________________________________

PR Errors:
______________

PR-ERR-P999: Text [HOST:MMDDHHMMSS]
101: Invalid [Attr Group Name] 
102: [Decommissioned 3/29/05]
103: Invalid [Attr Name]: [Attr Value]
104: Action would result in a merge of two DO-NOT-MERGE records.
105: Invalid number of [Attr Name] sent ([Num Sent]): can send between
     [Min Allowed] and [Max Allowed] at a time.
106: [PK Name -- USCID] field required.
107: No TYPE available although required for Attribute Group: [Attr Group Name]
108: Received multi value when single value expected
109: [SOR Name] attempted to write to the attribute ([Attr Name]) w/o
     Authority level
110: Invalid [USCID/GUID]: [USCID/GUID value]
111: Invalid XML, an unrecognized attribute was provided: [Attr Name]
112: An invalid XML function (Create, Update, etc.) was provided:
     [Function Name]
113: Provided a USCID/GUID on a Create: [USCID/GUID]
114: Did not provide a USCID/GUID on an Update
115: SOR provided USCID that does not exist in PR: [USCID]
116: The two USCIDs point to the same record: [USCID1], [USCID2]
117: Given SOR is not valid: [SOR Name]
118: [SOR Name] has no permission for given XML function: [XML function name]
119: SOR Provided a USCID to be set active that was never merged: [USCID]
120: Must specify one and only one action in XML (Create, Update, etc.)
121: SOR provided a USCID/GUID belonging to inactive, non-merged
     record: [USCID/GUID Value]
122: Request for Read did not result in one match; number of matches:
     [NUM OF MATCHES]
123: Cannot unmerge to records that aren't already merged: [USCID1], [USCID2]
124: Required dependency information missing for Attribute Group: [Attr Group Name]
125: Error while updating SOR data table: [error]
126: Error while computing current term: [error]
127: [Table name] cannot be updated by SORs
128: Did not provide iVIPID on a Create/Update
129: SOR did not provide information required for USCID request
130: SOR did not provide information required for person query
131: SOR did not provide information required for person create
201: Invalid SOR in DB.
202: Reached max insert tries for new record: always generated IDs that exist.
203: Invalid Meta Data.
204: Found an invalid Primary Key in Database.
205: Given RID not found in DB.
206: Attempt to delete Attribute Group. 
207: Value exists in DB without an SOR value associated with it.
208: Given USCID doesn't match any Merge RID.
209: Attribute in DB has no DTM stamp.
210: Internal looped too many times.
211: The given USCID is marked as having been merged into multiple records.
212: Received invalid request for special-case matching: [REQUEST]
213: Not yet implemented
214: Invalid SOR for balancing [SOR]
215: Invalid function [FUNCTION]
216: Called non-master on lock
217: Called non-master on release
301: General Error


------------------------------------------------


Repository design
___________________

Class (allow_merge)
 Group (allow_mult, has_type, has_depends)
  Attribute

Examples
__________

Person (allow_merge='Y')
 Name (allow_mult='N', has_type='Y', has_depends='N') 
  Last (type='Reported')

Person (allow_merge='Y')
 StudentMajor (allow_mult='Y', has_type='N', has_depends='Y') 
  Post (depends=['TermoCode'])

_____________________________________________________________________________
_____________________________________________________________________________
"""


#
# imports
#

import xml.dom.minidom
import unidecode
import threading
import traceback
import io
import datetime
import binascii
import string
import random
import socket
import types
import copy
import time
import sys
import re
import gc

from xml.sax import saxutils

from USC.WS.GoldenPR import prcomm  # web services interface
from USC.Util import Logger, DBToolsOX, Misc, Encrypt

from GPRUtils import Hooks

#
# Global objects
#

oInit = Misc.TConfig('ConfigPR.py')
oPreProc = Hooks.TPreProcessor(oInit)
oDeleteFilter = Hooks.TDeleteFilter()
oCreateFilter = Hooks.TCreateFilter()

#****************************************************************************
#
#  Repository generated errors
#
#****************************************************************************

class ERepository(Exception):
    strTmp = (str(socket.getfqdn())).split('.')
    strHost = (strTmp[0]).upper()

    def __init__(self, iErrorID, strText, strType='ERR', strAction=None):
        self.iErrorID = iErrorID
        self.strText = strText
        self.strType = strType
        self.strAction = strAction
        assert strType in ['ERR', 'INFO', 'ABORT'], 'Invalid Error Message Type'
        self.iTime = time.time()

    def __str__(self):
        return "PR-ERR-P%d: %s [%s:%s]" % (self.iErrorID, self.strText, self.strHost, time.strftime("%m%d%H%M%S", time.localtime(self.iTime)))

    def fGetErrorID(self):
        return self.iErrorID

    def fGetText(self):
        return self.strText

    def fGetType(self):
        return self.strType

    def fGetAction(self):
        return self.strAction

# Not currently used
class ERepositoryVerifyError(ERepository):
    
    def __init__(self, iErrorID, strText, **kw):
        ERepository.__init__(self, iErrorID, strText, kw.get('strType', 'ERR'))
        self.strAGName = kw.get('strAGName')
        self.strAttrName = kw.get('strAttrName')

    def fGetAGName(self):
        return self.strAGName

    def fGetAttrName(self):
        return self.strAttrName

    def fGetErrorID(self):
        return self.iErrorID
    
    def fGetText(self):
        return self.strText
    
    def fGetType(self):
        return self.strType
    
    def fGetTime(self):
        return self.iTime
        

#****************************************************************************
#
#  Contains Metadata for CLASS
#
#****************************************************************************

class TMClass:

    """
    Class meta data
    |
    |  table:
    |  --------------------
    |  meta_class
    |
    |  columns:      e.g.:
    |  --------------------
    |  name          Person
    |  allow_merge   Y
    """

    def __init__(self, strClassName, strAllowMerge):
        #self.iClassID = None
        self.strName = strClassName
        assert strAllowMerge in ['Y', 'N'], \
               "strAllowMerge must be Y or N: %s" % (strAllowMerge)
        self.strAllowMerge = strAllowMerge
        self.ctValidPKs = []
        #self.strNote = None
        self.ctMGroups = {}

    def fGetKey(self):
        return (self.strName,) 

    def fAddGroup(self, oGroup):
        self.ctMGroups[oGroup.fGetKey()] = oGroup

    def __str__(self):
        return "TMClass: %s" % (self.strName)


#****************************************************************************
#
#  Contains Metadata for GROUP
#
#****************************************************************************

class TMGroup:

    """
    Group meta data
    |
    |  table:
    |  --------------------
    |  meta_group
    |
    |  columns:      e.g.:
    |  ------------------------------------
    |  name                  StudentMajor
    |  class_id              id(Person)
    |  allow_mult            Y
    |  has_type              N
    |  has_depends           Y

    Groups can have:
      types
      multi-valued attributes
      dependencies (meaning all attributes in this group depend on
       some additional information that must be present when SOR sends
       updates for this group)

    Notes:
      * We maintain a dict of types, which contains valid values that
        a type can be (mapped to id in meta table)
      * We will also maintain a list of dependencies: this will
        correspond to data element(s) that must be present when SOR
        sends updates for this group of attributes
      * We will not maintain a list of what values each dependency can
        take, since those values need to be dynamically loaded
    
    """
    
    def __init__(self, oMClass, iGID, strGName, strAllowMult,
                 strHasTypes, strHasDepends, strNote = ''):
        self.oMClass = oMClass
        self.iGroupID = int(iGID)
        self.strName = strGName

        if strAllowMult not in ['Y', 'N']:
            raise ERepository(203,  "Invalid strAllowMult")
        self.strAllowMult = strAllowMult   # Y|N for now no need to
                                           # implement this

        if strHasTypes not in ['Y', 'N']:
            raise ERepository(203, "Invalid strHasTypes")
        self.strHasTypes = strHasTypes  # Y|N

        if strHasDepends not in ['Y', 'N']:
            raise ERepository(203, "Invalid strHasDepends")
        self.strHasDepends = strHasDepends  # Y|N
        
        self.strNote = strNote 
        self.ctMAttrs = {}
        self.ctTypes = {}

        #
        # store dependency e.g. "TermCode"
        #
        self.oMDepends = TMDepends() # our dependencies metadata object

        self._ctAttrNames = None
        self._ctTypeIDCache = {}  

    def __str__(self):
        return '(TMGroup: %s, [mult:%s|type:%s|depends:%s]; Types: %s; DependsOn: %s)' % \
               (self.strName,
                self.strAllowMult,
                self.strHasTypes,
                self.strHasDepends,
                str(self.ctTypes),
                str(self.oMDepends))
        
    def fGetAttrNames(self):
        if self._ctAttrNames is None:
            self._ctAttrNames = [j[0] for j in list(self.ctMAttrs.keys())]
            self._ctAttrNames.sort()
            self._ctAttrNames = tuple(self._ctAttrNames)
            
        return self._ctAttrNames

    def fHasTypes(self):
        return len(self.ctTypes) > 0

    def fType2TypeID(self, strType):
        return self.ctTypes[strType]

    def fTypeID2Type(self, iTypeID):
        return self._ctTypeIDCache[iTypeID] 

    def fGetKey(self):
        return (self.strName,)

    def fAddAttr(self, oAttr):
        self.ctMAttrs[oAttr.fGetKey()] = oAttr

    def fAddType(self, strType, iTypeID):
        self.ctTypes[strType] = iTypeID
        self._ctTypeIDCache[iTypeID] = strType

    def fHasDepends(self):
        return self.oMDepends.fHasDepends()


#****************************************************************************
#
#  Contains Metadata for dependencies (helper class for Group metadata)
#
#****************************************************************************

class TMDepends:

    """
    Attribute meta data
    |
    |  table:
    |  --------------------
    |  meta_depends
    |
    |  columns:      e.g.:
    |  --------------------
    |  group_id      id(StudentMajor)
    |  gdep_name     Term
    |  gdep_table    SOR_SIS_TERM
    |  gdep_col      TermCode
    """
    
    def __init__(self):
        self.ctDepends = {}
        self._ctDependsIDCache = {}

    def __str__(self):
        return str(self.ctDepends)

    def fHasDepends(self):
        return len(self.ctDepends) > 0

    def fGetKeys(self):
        return list(self.ctDepends.keys())

    def fGetItems(self):
        return list(self.ctDepends.items())

    def fKey2ID(self, strKey):
        return self.ctDepends[strKey]

    def fID2Key(self, iID):
        return self._ctDependsIDCache[iID] 

    def fAdd(self, strKey, iID):
        self.ctDepends[strKey] = iID
        self._ctDependsIDCache[iID] = strKey


#****************************************************************************
#
#  Contains Metadata for attributes
#
#****************************************************************************

class TMAttr:

    """
    Attribute meta data
    |
    |  table:
    |  --------------------
    |  meta_attr
    |
    |  columns:      e.g.:
    |  --------------------
    |  name          First_STRP
    |  group_id      id(Name)
    |  encrypt_id    1
    |  filter        ^[a-zA-Z \-'\.]*$
    |  auto_gen_func STRP
    |  auto_gen_p1   First
    """
    
    def __init__(self, oMGroup, iAttrID, strAttrName, strEncrDataID,
                 strFilter, strAutoGenAttr, strAutoGenP1, oEncrypt,
                 strNote=''):
        self.oMGroup = oMGroup
        self.iAttrID = int(iAttrID)
        self.strName = strAttrName
        self.strEncrDataID = strEncrDataID
        self.strFilter = strFilter
        self.strAutoGenAttr = strAutoGenAttr
        self.strAutoGenP1 = strAutoGenP1
        self.oEncrypt = oEncrypt
        self.oFilter = None
        if (self.strFilter is not None) and (len(self.strFilter) > 0):
            self.oFilter = re.compile(self.strFilter)

        self.strLongName = '%s.%s' % (self.oMGroup.strName, self.strName)
        
        self.strNote = strNote
        self.ctAuthLevels = {}

    def fGetKey(self):
        return (self.strName,)

    def fAddAuthLevel(self, iSORID, iAuthLevel, strReadTrans = None, iGType = None):
        self.ctAuthLevels[(iSORID, iGType)] = (iAuthLevel, strReadTrans)

    def fGetAuthLevel(self, iSORID, iGType = None):
        return self.ctAuthLevels.get((iSORID, iGType), (None, None))


#****************************************************************************
#
#  General purpose Object (derived from MClass)
#
#****************************************************************************

class TObject:

    """
    fCopyShell
    fAddPK
    fAddEPK
    fAddHistoricalEPKs
    fAddMultiVal
    fAddEmptyDepMultiVal
    fAddAG
    fUpdate
    """
    
    def __init__(self, oMClass):
        self.oMClass = oMClass
        self.ctAttrGroups = {}
        self.ctPKs = {}   # generated keys
        self.ctEPKs = {}  # encrypted PKs
        self.ctHistoricalPKs = []
        self.iRID = None
        self.oCreateDTM = None
        self.oModifiedDTM = None
        self.strIsActive = None
        self.strNote = None
        self.strID = None

    def fCopyShell(self):
        oCopy = TObject(self.oMClass)
        return oCopy

    def fAddPK(self, strPKName, strValue, oEncrypt):
        if len(strValue) == 0: raise ERepository(106, "%s field required" % (strPKName))
        self.ctPKs[strPKName] = strValue
        strEValue = oEncrypt.fEncrypt(oInit.golden.strPKsEncryptType, strValue)
        self.ctEPKs[strPKName] = strEValue
        # print('Added PK:', strValue, strEValue)

    def fAddEPK(self, strPKName, strEValue, oEncrypt):
        if len(strEValue) == 0: raise ERepository(204, "Invalid (EPK) %s value" % (strPKName))
        self.ctEPKs[strPKName] = strEValue
        strValue = oEncrypt.fDecrypt(strEValue)
        self.ctPKs[strPKName] = strValue
        # print('added EPK:', strEValue, strValue)

    def fAddHistoricalEPKs(self, ctEPKs, oEncrypt):
        if len(ctEPKs) != len(self.oMClass.ctValidPKs):
            raise ERepository(204, "Invalid (EPKs) %s " % ((list(ctEPKs.keys()))))

        ctKey = {}
        for strKey in self.oMClass.ctValidPKs:
            # print('Inside fAddHistoricalEPKs: Start of for loop')
            if strKey not in ctEPKs:
                raise ERepository(204, "Invalid (EPKs) %s is missing " % (strKey))
            strEValue = ctEPKs[strKey]
            strValue = oEncrypt.fDecrypt(strEValue)
            ctKey[strKey] = strValue
            # print('Inside fAddHistoricalEPKs: End of for loop')

        self.ctHistoricalPKs.append(ctKey)

    #------------------------------------------------------------------------
    #
    #  Add empty container for multi-valued groups.
    #
    #  Notes:
    #    1) The reason that this method exists (in addition to fAddAG)
    #       is that it will be called even if no attributes are found in
    #       a group, and is really a way for deleting attributes from
    #       multi-valued attribute groups.
    #    2) The above worked fine 'til we added group dependencies:
    #       dependencies work similarly to types & the reason the above
    #       solution worked is 'cause groups are either typed or multi-valued
    #       & never both at the same time. Now with dependencies, we can
    #       have dependent attributes in combination with either types or
    #       multi-valued attribuites. To solve THAT problem, see method
    #       fAddEmptyDepMultiVal.
    #
    #------------------------------------------------------------------------
    def fAddMultiVal(self, oMGroup):
        if oMGroup is None:
            return

        ctKey = oMGroup.fGetKey()
        if ctKey not in self.ctAttrGroups:
            self.ctAttrGroups[ctKey] = []

    #------------------------------------------------------------------------
    #
    #  Used for multi-valued attribute groups with dependencies.
    #
    #  For details see comments for method fAddMultiVal.
    #
    #------------------------------------------------------------------------
    def fAddEmptyDepMultiVal(self, oAG):
        if oAG is None:
            return

        ctKey = oAG.oMGroup.fGetKey()

        for dkey, dval in oAG.oDepends.fGetGivenItems():
            ctKey += ((dkey,dval),)
        
        if ctKey not in self.ctAttrGroups:
            self.ctAttrGroups[ctKey] = []

    def fAddAG(self, oAG):
        if oAG is None:
            return
        
        if not oAG.fVerify():
            raise ERepository(101, "Invalid %s" % (oAG.oMGroup.strName))
        
        ctKey = oAG.fGetKey()
        # print('AG KEY:', ctKey)
        if ctKey not in self.ctAttrGroups:
            self.ctAttrGroups[ctKey] = []
            
        #
        # This accommodates multi-values (assumed check for allow_mult
        # already done).
        #
        self.ctAttrGroups[ctKey].append(oAG)

    #------------------------------------------------------------------------
    #
    #  Can be implemented in sub-classes
    #  Updates record to fix data, etc.
    #
    #------------------------------------------------------------------------
    def fUpdate(self):
        return
    
    def __str__(self):
        strRet =  "%s - %s: %s" % (self.oMClass.strName, str(self.iRID), str(self.ctPKs))
        strRet += "\n  Historical PKs: %s" % (str(self.ctHistoricalPKs))
        for ctAG in list(self.ctAttrGroups.values()):
            for oAG in ctAG:
                strRet +=  "\n  %s, %s:" % (oAG.oMGroup.strName, oAG.strType)
                strRet +=  "\n  Dependencies: %s:" % (oAG.oDepends.fGetGivenItems())
                for oAttr in list(oAG.ctAttrs.values()):
                    strRet += "\n    %s = %s" % (oAttr.oMAttr.strName, oAttr.strValue)
        return strRet


#****************************************************************************
#
#  General purpose attribute group (derived from MGroup)
#
#****************************************************************************

class TAttrGroup:

    """
    fIsSame
    fCopyShell
    fAutoGenStrip
    fRunAutoGen
    fVerify
    fGetAttrNames
    fGetKey
    fAddAttr

    Notes:
    * "Type" is not an attribute that is maintained by the SORs, it's
      values are hardcoded in metadata & do not get get updated by the
      SORs
    * "TermCode" is not an attribute, it's more akin to Type field
      except that it is indirectly updated by the SOR(s). "TermCode"
      itself is hardoced in metadata, and the metadata has pointer to
      table that maintains the values for "TermCode"
    * Unlike Type, we can have many dependencies
    * In addition to storing dependencies, should also store the
      actual allowable values for these dependencies
    
    """

    def __init__(self, oMGroup):
        self.oMGroup = oMGroup
        self.ctAttrs = {}
        self.iRID = None
        self.oCreateDTM = None
        self.oModifiedDTM = None
        self.strType = None
        self.strNote = None
        self.strID = None
        self.oDepends = None
        self.bDeleted = 0
        #self.bRanAutoGen = 0
        self._ctAttrNames = None
        self.bOverrideAndAllowDelete = False

        # Create an empty shell for depends info
        self.fInitDepends()

    def fInitDepends(self):
        self.oDepends = TDepends()
    
    def fIsSame(self, oAG):
        if oAG is None:
            return 0
        if self.oMGroup != oAG.oMGroup:
            return 0
        if self.strType != oAG.strType:
            return 0

        #
        # Match given dependency values
        #
        if self.oMGroup.fHasDepends():
            if not self.oDepends:
                # should not happen since depends should've
                # been instantiated by now
                return 0
            for dkey, dval in self.oDepends.fGetGivenItems():
                if dval != oAG.oDepends.fGetGivenValue(dkey):
                    return 0

        ctKeys1 = list(self.ctAttrs.keys())
        ctKeys2 = list(oAG.ctAttrs.keys())
        ctKeys1.sort()
        ctKeys2.sort()
        if ctKeys1 != ctKeys2:
            return 0

        for ctKey in ctKeys1:
            if not self.ctAttrs[ctKey].fIsSame(oAG.ctAttrs[ctKey]):
                return 0

        return 1

    def fCopyShell(self):
        oCopy = TAttrGroup(self.oMGroup)
        oCopy.strType = self.strType
        
        #
        # Note: following will have depends info
        # assuming fLoadGroupDepends has been run
        oCopy.oDepends = self.oDepends.fCopyShell()
        oCopy.oDepends = self.oDepends.fUpdateShell(oCopy.oDepends)
        
        return oCopy

    def fAutoGenStrip(self, strIn):
        strIn = re.sub(r'[^a-zA-Z]', '', strIn)
        strIn = strIn.lower()
        return strIn

    def fRunAutoGen(self):
        #if self.bRanAutoGen != 1:
        #    return

        for oMAttr in list(self.oMGroup.ctMAttrs.values()):
            if oMAttr.strAutoGenAttr == 'STRP':
                strAttrSrc = oMAttr.strAutoGenP1
                # make sure to delete it first, just incase there's junk
                strDestKey = (oMAttr.strName,)
                if strDestKey in self.ctAttrs:
                    del self.ctAttrs[strDestKey]
                
                oAttrSrc = self.ctAttrs.get((strAttrSrc,), None)
                if oAttrSrc:
                    if oAttrSrc.strValue is not None:
                        oAttrDst = TAttr(oMAttr)
                        oAttrDst.strValue = self.fAutoGenStrip(oAttrSrc.strValue)
                        oAttrDst.strSOR = 'PR'
                        oAttrDst.fEncrypt()
                        self.fAddAttr(oAttrDst)                        

        #self.bRanAutoGen = 1        

    def fVerify(self):
        self.fRunAutoGen()
        
        # make sure it's not just an empty shell
        if len(self.ctAttrs) == 0:
            return 0

        # make sure has valid TYPE if required
        if self.oMGroup.fHasTypes():
            if self.strType not in self.oMGroup.ctTypes:
                return 0
        else:
            if self.strType is not None:
                return 0

        # make sure has valid DEPENDENCIES if required
        if self.oMGroup.fHasDepends():
            #
            # 1) Make sure all dependencies are present:
            #    In other words:
            #    a) given & valid dependency keys exist
            #    b) given & valid dependency keys match
            # 2) For each given key, make sure the value is valid
            #
            if not self.oDepends:
                # should not happen since depends should've
                # been instantiated by now
                return 0
            if not self.oDepends.fHasGivens():
                return 0
            if not self.oDepends.fHasValids():
                return 0

            ctGivenKeys = self.oDepends.fGetGivenKeys()
            ctGivenKeys.sort()
            ctValidKeys = self.oDepends.fGetValidKeys()
            ctValidKeys.sort()
            if ctGivenKeys != ctValidKeys:
                return 0
            
            for given_name, given_value in self.oDepends.fGetGivenItems():
                # not necessary since done, but...
                if not self.oDepends.fHasValidKey(given_name):
                    return 0
                # Note, fGetValidValue returns a list or None (plus the regex-filter)
                (valid_values, valid_filter) = self.oDepends.fGetValidValue(given_name)
                # validate
                if valid_filter:
                    valid_filter = re.compile(valid_filter)
                    if not valid_filter.match(given_value):
                        return 0
                if valid_values is None:
                    # nothing to verify, so assume anything allowed (?)
                    pass
                elif given_value not in valid_values:
                    return 0
        else:
            #
            # has no dependencies..
            #
            if self.oDepends is not None:
                if self.oDepends.fHasValids():
                    return 0
                if self.oDepends.fHasGivens():
                    return 0

        # make sure attributes are OK
        for oAttr in list(self.ctAttrs.values()):
            if not oAttr.fVerify():
                return 0
            
        return 1

    def fGetAttrNames(self):
        if self._ctAttrNames is None:
            self._ctAttrNames = [j[0] for j in list(self.ctAttrs.keys())]
            self._ctAttrNames.sort()
            self._ctAttrNames = tuple(self._ctAttrNames)
            
        return self._ctAttrNames

    def fGetKey(self):
        #
        # Attribute group will be keyed by:
        #   Group name, Group type (if any), Group dependencies (if any)
        #
        
        if not self.fVerify():
            raise ERepository(101, "Invalid %s" % (self.oMGroup.strName))

        bHasTypes = self.oMGroup.fHasTypes()
        bHasDepends = self.oMGroup.fHasDepends()

        if not bHasTypes and not bHasDepends:
            return self.oMGroup.fGetKey()
        
        ctKey = self.oMGroup.fGetKey()
        
        if bHasTypes:
            if self.strType is None:
                raise ERepository(107, "No Type available for typed AttrGroup: %s" % (self.oMGroup.strName))
            else:
                ctKey += (self.strType,)
        if bHasDepends:
            # should not happen (since we always instantiate)
            if not self.oDepends:
                raise ERepository(124, "Required dependency information missing for dependent AttrGroup: %s" % (self.oMGroup.strName))
            if not self.oDepends.fHasGivens():
                raise ERepository(124, "Required dependency information missing for dependent AttrGroup: %s" % (self.oMGroup.strName))
            else:
                for given_name, given_value in self.oDepends.fGetGivenItems():
                    # need to be able to distinguish dependencies...
                    ctKey += ((given_name, given_value),)

        return ctKey
    
    def fAddAttr(self, oAttr):
        self.ctAttrs[oAttr.fGetKey()] = oAttr
        self._ctAttrNames = None

    def __str__(self):
        strRet =  "%s - %s:" % (self.oMGroup.strName, str(self.iRID))
        for oAttr in list(self.ctAttrs.values()):
            strRet += "\n\t%s" % (str(oAttr))
        return strRet


#****************************************************************************
#
#  General purpose dependencies (helper class for AttrGroup)
#
#****************************************************************************

class TDepends:
    """
    Need to maintain 2 dicts for dependencies:
     1) Store dependencies and list of values that each
        dependency can take (if list is empty should allow any
        value)
     2) Store dependencies and value provided by SOR for each
        dependency
    """
    
    def __init__(self):
        self.ctValid = {}
        self.ctGiven = {}

    def fCopyShell(self):
        oCopy = TDepends()
        return oCopy

    def fUpdateShell(self, oCopy):
        oCopy.ctValid = copy.deepcopy(self.ctValid)
        oCopy.ctGiven = copy.deepcopy(self.ctGiven)
        return oCopy

    #
    # Getter/setter methods for valid dependencies
    #
    
    def fGetValidValue(self, strKey):
        return self.ctValid[strKey]
    
    def fSetValidItem(self, strKey, ctValue=None, strFilter=None):
        self.ctValid[strKey] = (ctValue, strFilter)
    
    def fGetValidKeys(self):
        return list(self.ctValid.keys())
    
    def fGetValidValues(self):
        return list(self.ctValid.values())
    
    def fGetValidItems(self):
        return list(self.ctValid.items())
    
    #
    # Getter/setter methods for given dependencies
    #
    
    def fGetGivenValue(self, strKey):
        return self.ctGiven[strKey]

    def fSetGivenItem(self, strKey, strValue):
        self.ctGiven[strKey] = strValue

    def fGetGivenKeys(self):
        return list(self.ctGiven.keys())

    def fGetGivenValues(self):
        return list(self.ctGiven.values())

    def fGetGivenItems(self):
        return list(self.ctGiven.items())

    #
    # misc
    #
    
    def fHasValidKey(self, strKey):
        return strKey in self.ctValid

    def fHasValids(self):
        return len(self.ctValid) > 0

    def fHasGivenKey(self, strKey):
        return strKey in self.ctGiven

    def fHasGivens(self):
        return len(self.ctGiven) > 0


#****************************************************************************
#
#  General purpose attribute (derived from MAttr)
#
#****************************************************************************

class TAttr:

    """
    fIsSame
    fCopyShell
    fVerify
    fEncrypt
    fDecrypt
    fGetKey
    """
    
    def __init__(self, oMAttr):
        self.oMAttr = oMAttr
        self.strValue = None
        self.strDBValue =  None
        self.oDTM = None
        self.strSOR = None

    def fIsSame(self, oA):
        if oA is None:
            return 0
        if self.oMAttr != oA.oMAttr:
            return 0
        if self.strValue != oA.strValue:
            return 0
        return 1

    def fCopyShell(self):
        oCopy = TAttr(self.oMAttr)
        return oCopy

    def fVerify(self):
        # change None to empty string:
        if self.strValue is None:
            self.strValue = ''

        # allow empty values:
        if len(self.strValue) == 0:
            return 1

        # if no filter, let through:
        if self.oMAttr.oFilter is None:
            return 1

        # if there IS a filter, and a value, test:
        if not self.oMAttr.oFilter.match(self.strValue):
            raise ERepository(103, "Invalid %s: %s" % (self.oMAttr.strLongName, self.strValue))
            
        return 1

    def fEncrypt(self):
        if self.oMAttr.strEncrDataID != '-1':
            self.strDBValue = self.oMAttr.oEncrypt.fEncrypt(self.oMAttr.strEncrDataID, self.strValue)
        else:
            if (self.strValue is not None):
                self.strDBValue = self.strValue
            else:
                self.strDBValue = ""

    def fDecrypt(self):
        if self.oMAttr.strEncrDataID != '-1':
            self.strValue = self.oMAttr.oEncrypt.fDecrypt(self.strDBValue) #self.strDBValue[2:]
        else:
            # this code isn't getting called anyway when the DB result was null
            if (self.strDBValue is not None):
                self.strValue = self.strDBValue
            else:
                self.strValue = ""

    def fGetKey(self):
        return (self.oMAttr.strName,)

    def __str__(self):
        strRes = "%s - %s (%s: %s)" % (self.oMAttr.strName, str(self.strValue),
                                       str(self.strSOR), str(self.oDTM))
        return strRes


#****************************************************************************
#
#  TSemaphoreServer: Serves semaphor requests
#
#  *** Not currently used
#
#****************************************************************************

class TSemaphoreServer(Misc.TThreaded):

    """
    To be used in load balancing situation - not currently used
    """

    iMaxLockTime = 120  # need to take into account prcomm's 7 second max timeout?
    
    def __init__(self, oLog = Logger.TLogger('SemaphoreServer',
                                             iPrintLevel=0,
                                             strToEmail=oInit.golden.strErrorNotifyFull),
                 ctOtherHosts = [], iPort = 12334, strKey='symkey_BALANCE'):
        Misc.TThreaded.__init__(self)
        self.oLog = oLog
        self.ctOtherHosts = ctOtherHosts
        self.iPort = iPort
        self.strKey = strKey

        self.strStatus = None  # 'Slave', 'Master'
        self.strMasterHost = None
        self.oStatusLock = threading.Lock()
        
        self.iLastPing = None
        self.iLastCleanup = 0

        self.ctLockedIDs = {}
        self.oIDsLock = threading.Lock()

        self.oWS = prcomm.TServer(self.fHandleRequest, self.iPort)


    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fPing(self):
        self.oLog.fDebug('Inside fPing', 5)
        strReq = "PNG:"

        iMaxErrorCount = random.choice(list(range(5, 10)))
        iErrorCount = 0
        iLoopCounter = 0
        while 1:
            iLoopCounter += 1
            if iLoopCounter > 50:
                raise ERepository(210, "Internal looped too many times: fPing")
            
            bFoundError = 0
            bFoundMaster = 0

            # check other hosts to see if any one of them is a master:
            for strHost in self.ctOtherHosts:
                strRes = self.fRequest(strReq, strHost)
                strRes = self.fXML2Text(strRes)
                # found master, done:
                if strRes == 'Master':
                    self.strMasterHost = strHost
                    self.strStatus = 'Slave'
                    bFoundMaster = 1
                    break

                # found a slave, okay, but continue:
                elif strRes == 'Slave':
                    continue

                # if there's an error, set flag, but continue
                else:
                    if bFoundError == 0:
                        bFoundError = 1
                        self.oLog.fDebug('Error Found in fPing', 5)
                        iErrorCount += 1
                    continue

            # if found a master, done:
            if bFoundMaster == 1:
                break

            # if no errors, but no master either, set to slave.  or... if too many errors do same thing:
            if (bFoundError == 0) or (iErrorCount > iMaxErrorCount):
                self.strStatus = 'Master'
                self.strMasterHost = None
                break

            time.sleep(random.random())
               

        # set clock for last ping:
        self.iLastPing = time.time()

    #------------------------------------------------------------------------
    #
    #  ctIDs - a bunch of strings -- all need to be free to succeed
    #  bBlocking: 1=blocking, 0=nonblocking (blocking doesn't work yet)
    #  ret val: 0 = successfully locked  1: can't lock (on non-blocking only)
    #
    #------------------------------------------------------------------------
    def fLock(self, ctIDs, bBlocking=1):
        self.oLog.fDebug('fLock: %s. bBlocking: %d. Status: %s' % (str(ctIDs), bBlocking, self.strStatus), 5)
        assert bBlocking == 0, "Must call as non-blocking"

        iLoopCounter = 0
        while 1:
            iLoopCounter += 1
            if iLoopCounter > 50:
                raise ERepository(210, "Internal looped too many times: fLock")
            
            if self.strStatus == 'Master':
                self.oLog.fDebug('Master: Acquire oIDsLock', 5)
                self.oIDsLock.acquire()
                self.oLog.fDebug('oIDsLock Acquired', 5)
                try:
                    bFoundHold = 0
                    # for each match:
                    for strID in ctIDs:
                        # check if it's on hold, if so, sleep for a bit and continue
                        if strID in self.ctLockedIDs:
                            bFoundHold = 1
                            break

                    if bFoundHold:
                        try:
                            self.oLog.fDebug('Inner oIDsLock release', 5)
                            self.oIDsLock.release()
                            self.oLog.fDebug("Inner oIDsLock released OK", 5)
                        except:
                            self.oLog.fDebug("Inner oIDsLock release FAILED", 5)
                            pass
                        
                        if bBlocking == 1:
                            time.sleep(0.3)
                            continue
                        else:
                            return 1

                    # if not, put all on hold and return matches
                    iTime = time.time() + self.iMaxLockTime
                    for strID in ctIDs:
                        self.ctLockedIDs[strID] = iTime

                    return 0

                finally:
                    try:
                        self.oLog.fDebug('Finally oIDsLock release', 5)
                        self.oIDsLock.release()
                        self.oLog.fDebug("Finally oIDsLock released OK", 5)
                    except:
                        self.oLog.fDebug("Finally oIDsLock release FAILED", 5)
                        pass
                

            elif self.strStatus == 'Slave':
                strReq = 'LCK:%d,%s' % (bBlocking, ','.join(ctIDs))
                try:
                    strRes = self.fRequest(strReq, self.strMasterHost)
                    if strRes.find('<RES>ok</RES>') >= 0:
                        return 0

                    elif strRes.find('<RES>blocked</RES>') >= 0:
                        return 1
                    
                    else:
                        self.strStatus = None
                    
                except:
                    self.strStatus = None

            else:
                self.fPing()

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fRelease(self, ctIDs):
        self.oLog.fDebug('fRelease: %s.  Status: %s' % (str(ctIDs), self.strStatus), 5)

        iLoopCounter = 0
        while 1:
            iLoopCounter += 1
            if iLoopCounter > 50:
                raise ERepository(210, "Internal looped too many times: fRelease")
            
            if self.strStatus == 'Master':
                self.oLog.fDebug('Master: Acquire oIDsLock', 5)
                self.oIDsLock.acquire()
                self.oLog.fDebug('oIDsLock Acquired', 5)
                try:
                    # for every match:
                    for strID in ctIDs:
                        # release from hold
                        del self.ctLockedIDs[strID]

                finally:
                    self.oLog.fDebug('Finally oIDsLock release', 5)
                    self.oIDsLock.release()
                    self.oLog.fDebug("Finally oIDsLock released OK", 5)
                    break

            elif self.strStatus == 'Slave':
                strReq = 'RLS:%s' % (','.join(ctIDs))
                try:
                    strRes = self.fRequest(strReq, self.strMasterHost)
                    if strRes.find('<RES>ok</RES>') >= 0:
                        break
                    else:
                        self.strStatus = None
                    
                except:
                    self.strStatus = None

            if self.strStatus is None:
                self.fPing()

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fCleanup(self):
        iTime = time.time()
        self.oLog.fDebug('Acquire: oIDsLock', 5)
        self.oIDsLock.acquire()
        self.oLog.fDebug('oIDsLock Acquired', 5)
        try:
            for (strID, iTimeToRelease) in list(self.ctLockedIDs.items()):
                if iTime > iTimeToRelease:
                    del self.ctLockedIDs[strID]
        finally:
            try:
                self.oLog.fDebug('Finally oIDsLock release', 5)
                self.oIDsLock.release()
                self.oLog.fDebug("Finally oIDsLock released OK", 5)
            except:
                self.oLog.fDebug("Finally oIDsLock release FAILED", 5)
                pass
        self.iLastCleanup = iTime

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fRequest(self, strReq, strHost):
        return self.oWS.fInvoke("<REQ>%s</REQ>" % (strReq),
                                    "http://%s:%i" % (strHost, self.iPort),
                                    self.strKey)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fHandleRequest(self, strReq, strSOR):
        self.oLog.fDebug('Inside fHandleRequest: Status: %s' % (self.strStatus), 5)
        strRet = None
        try:
            strRes = None
            if strSOR != 'BALANCE':
                raise ERepository(214, 'Invalid SOR for balancing: %s' % (strSOR))

            strText = self.fXML2Text(strReq)

            strFunc = strText[:3]
            strQuery = strText[4:]
            if strFunc == 'PNG':
                strRes = self.fHandlePing()
            elif strFunc == 'LCK':
                strRes = self.fHandleLock(strQuery.split(','))
            elif strFunc == 'RLS':
                strRes = self.fHandleRelease(strQuery.split(','))
            else:
                raise ERepository(215, 'Invalid function: %s' % (strFunc))

            strRet = "0|<RES>%s</RES>" % (strRes)
        
        except:
            self.oLog.fError('fHandleRequest: Found Exception', 3)
            strRet =  "1|%s" % (str(sys.exc_info()[1]))

        self.oLog.fDebug('Inside GPRTools.py[TSemaphoreServer::fHandleRequest] Returning: %s' % (strRet), 5)
        return strRet

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fXML2Text(self, strReq):
        if strReq.find('SOAP-ENV:Client') >= 0:
            return ''
        
        strText = ((str(strReq)).split('\n'))[1]
        strText = strText[5:-6]
        return strText
    
##         self.oLog.fDebug('text: %s'% (strText), 5)
##         hXMLFile = StringIO.StringIO(strReq)
##         self.oLog.fDebug('Analyzing XML2', 5)
##         oNode = xml.dom.minidom.parse(hXMLFile)
##         self.oLog.fDebug('Analyzing XML3', 5)
##         strText = ""
##         oNode = oNode.childNodes[0]
##         for oSubNode in oNode.childNodes:
##             if oSubNode.nodeType == oSubNode.TEXT_NODE:
##                 strText += oSubNode.data
                
##         strText = (str(strText)).strip()
##         self.oLog.fDebug('Analyzing XML4: %s'% (str(strText)), 5)
##         del hXMLFile
##         del oNode
##         gc.collect()
##         return strText
        
        
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fHandlePing(self):
        self.oLog.fDebug('Inside fHandlePing: %s' % (str(self.strStatus)), 5)
        return str(self.strStatus)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fHandleLock(self, ctIDs):
        self.oLog.fDebug('Inside fHandleLock', 5)
        bBlocking = int(ctIDs[0])
        del ctIDs[0]
        if self.strStatus == 'Master':
            iRet = self.fLock(ctIDs, bBlocking)
            self.oLog.fDebug('Check iRep', 5)
            if iRet == 0:
                return 'OK'
            else:
                return 'BLOCKED'
            
        raise ERepository(216, 'Called non-master on lock')

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fHandleRelease(self, ctIDs):
        self.oLog.fDebug('Inside fHandleRelease', 5)
        if self.strStatus == 'Master':
            self.fRelease(ctIDs)
            return 'OK'
        raise ERepository(217, 'Called non-master on release')


    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fRun_thread(self):
        self.oLog.fDebug('Inside fRun_thread', 5)
        self.fPing()
        self.oWS.fStart()
        iSleepTime = random.choice(list(range(18, 24)))
        
        while 1:
            if self.fShouldExit():
                self.oWS.fStop()
                return

            if (time.time() - self.iLastPing) > iSleepTime:
                self.fPing()
                iSleepTime = random.choice(list(range(18, 24)))

            if (time.time() - self.iLastCleanup) > 1:
                self.fCleanup()

            self.fSleepHeartbeat()
    


#****************************************************************************
#
#  General purpose interface with repository
#
#  Interface with DB
#  Given dict, update DB
#
#****************************************************************************

class TORInterface:

    #
    # sql
    #

    # fGetMatches:
    sqlSelectMatchesPKs = """
       select p.RID, p.Active_Flag
       from %s p
       where %s
       """

    sqlSelectMergedFinalID = """
       select pm.FINAL_RID
       from %s_MERGE pm
       where pm.MERGED_RID = ?
       """

    # fCreateRecordShell:
    sqlSelectNextRID = """
       select SEQ_%s_RID.nextval from dual
       """

    sqlGenerateGUID = "select sys_guid() from dual"
    
    sqlInsertRecordShell = """
       insert into %s
       (ID, RID, GUID, USCID, CREATE_DTM, MODIFIED_DTM, ACTIVE_FLAG, NOTE)
       values (SEQ_IDS.nextval, ?, ?, ?, sysdate, sysdate, 'Y', ?)
       """

    # fUpdateRecordShell
    sqlUpdateRecordShell = """
       update %s
       set MODIFIED_DTM = sysdate,
           NOTE = ?
       where RID = ?
       """

    # fReadRecordShell
    sqlSelectRecordShell = """
       select %s, CREATE_DTM, MODIFIED_DTM, ACTIVE_FLAG, NOTE
       from %s
       where RID = ?
       """

    # fReadRecordHistory
    sqlSelectRecordHistory = """
       select {0}, {1}
       from {2} p, {3}_MERGE pm
       where p.RID = pm.MERGED_RID
       and pm.final_rid = ?
       """

    # fReadRecordMGroup
    sqlSelectGroup = """
       select %s
       from %s_%s
       where RID = ?
       """

    # fSetup_Meta:
    sqlSelectClasses = """
       select CLASS_ID, CLASS_NAME, ALLOW_MERGES, NOTE
       from META_CLASS
       """

    sqlSelectClassPKs = """
       select ATTR_NAME
       from META_CLASS_PK
       where CLASS_ID = ?
       """
    
    sqlSelectDEs = """
       select GROUP_ID, GROUP_Name, ALLOW_MULTIPLE, HAS_TYPES, HAS_DEPENDS, NOTE
       from META_GROUP
       where CLASS_ID = (select CLASS_ID from META_CLASS where CLASS_ID=?)
       """

    sqlSelectTypes = """
       select GTYPE_ID, GTYPE_Name
       from META_GROUP_TYPE
       where GROUP_ID = ?
       """

    #
    # sql queries related to group dependencies
    #
    sqlSelectDepends = """
       select GDEP_ID, GDEP_Name
       from META_GROUP_DEPENDS
       where GROUP_ID = ?
       """
    sqlSelectDependsMetaInfo = """
      select GDEP_Table, GDEP_Col, FILTER
      from META_GROUP_DEPENDS
      where GDEP_ID = ? and GROUP_ID = ?
      """
    sqlSelectDependsValidValues = """
      select distinct %s
      from %s
      """

    sqlSelectAttrs = """
       select a.ATTR_ID, a.ATTR_Name, e.DATA_ID, a.FILTER, a.AUTO_GEN_FUNC, a.AUTO_GEN_P1
       from META_ATTR a, META_ENCRYPT e
       where a.GROUP_ID = ?
       and e.ENCRYPT_ID = a.ENCRYPT_ID
       """

    sqlSelectAttrAuth = """
       select SOR_ID, GTYPE_ID, WRITE_LEVEL, READ_TRANS
       from META_ATTR_AUTHORITY
       where ATTR_ID = ?
       """

    # fSetup_SORs:
    sqlSelectSORs = """
       select SOR_ID, SOR_Name
       from META_SOR
       """

    sqlSelectSORFuncAuthority = """
       select ms.SOR_Name, mf.func_name
       from meta_func mf, meta_func_authority mfa, meta_sor ms
       where mfa.sor_id = ms.sor_id
       and   mfa.func_id = mf.func_id
       """
    
    # fReadAG:
    sqlSelectAG = """
       select RID, CREATE_DTM, MODIFIED_DTM, NOTE, ID, %s
       from %s_%s
       where RID = ?
       """

    # fInsertAG:
    sqlInsertAG = """
       insert into %s_%s
       (ID, RID, CREATE_DTM, MODIFIED_DTM, NOTE, %s)
       values (SEQ_IDS.nextval, ?, sysdate, sysdate, ?, %s)
       """

    sqlUpdateAG = """
       update %s_%s
       set MODIFIED_DTM = sysdate,
           NOTE = ?%s
       where ID = ?
       """

    sqlDeleteAG = """
       delete from %s_%s
       where ID = ?
       """

    # fSetActiveFlag
    sqlUpdateActiveFlag = """
       update %s
       set Active_Flag = ?,
           Modified_DTM = sysdate
       where RID = ?
       """

    # fClearRecordData
    sqlDeleteRecordData = """
       delete from %s
       where RID = ?
       """
    
    sqlSelectSORPKs = """
       select ms.SOR_NAME, ma.ATTR_NAME
       from META_SOR_PK mpk, META_SOR ms, META_ATTR ma
       where ms.SOR_ID = mpk.SOR_ID
       and ma.ATTR_ID = mpk.ATTR_ID
       """
    
    #------------------------------------------------------------------------
    #  c'tor
    #------------------------------------------------------------------------
    def __init__(self, oLog=Logger.TLogger('TGoldenPRServer', 'GoldenPR_Debug',
                                     iPrintLevel=oInit.golden.iPrintLevel,
                                     iRecycleKeep=oInit.golden.iRecycleKeep,
                                     bDisableConsole=1,
                                     strToEmail=oInit.golden.strErrorNotifyFull)):
        self.oLog = oLog
        self.oSrLog = Logger.TLogger('TGoldenPRServer', 'GoldenPR_SilverRule',
                                     iPrintLevel=oInit.golden.iPrintLevel,
                                     iRecycleKeep=oInit.golden.iRecycleKeep,
                                     bDisableConsole=1,
                                     strToEmail=oInit.golden.strErrorNotifyFull)

        self.oDB = None
        self.oLockAdd = threading.Lock()
        self.oLockSetup = threading.Lock()
        self.oLockMatches = threading.Lock()
        self.ctRIDsOnHold = {}
        self.iLastConnect = None
        self.ctMClasses = None
        self.ctSOR2ID = None
        self.ctID2SOR = None

        self.ctGroupDependsCache = {}

        # self.oSemSrv = TSemaphoreServer(self.oLog, oInit.golden.ctOtherHosts, oInit.golden.iSemSrvPort)
        # self.oSemSrv.fStart()

        self.oProf = Logger.TProfiler('GPRTools', bDoProfiling=oInit.golden.bDoProfiling, oLog=self.oLog)

        # setup encryption:
        self.oEncrypt = Encrypt.TEncrypt(oInit.golden.ctEncryptKeys)

        # setup meta data:
        self.bSetup = 0

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    ##def __del__(self):
    ##    # self.oSemSrv.fStop()
    ##    pass
        
    #------------------------------------------------------------------------
    #
    #  Setup database related things NOT on startup.
    #
    #------------------------------------------------------------------------
    def fSetup(self):
        self.oLog.fDebug('Inside fSetup', 5)
        self.oLog.fDebug('fSetup: oLockSetup Before Acquire', 5)
        self.oLockSetup.acquire()
        self.oLog.fDebug('fSetup: oLockSetup Acquired', 5)
        try:
            self.oLog.fDebug('Inside fSetup TRY block', 5)
            if not self.bSetup:
                self.oLog.fDebug('TRUE - not self.bSetup', 5)
                self.fConnect()
                self.fSetup_SORs()
                self.fSetup_Meta()
                self.fSetup_Util()
                self.fSetup_Query()
                self.bSetup = 1
            else:
                self.oLog.fDebug('FALSE - not self.bSetup', 5)

        finally:
            self.oLog.fDebug('fSetup: oLockSetup Before Release', 5)
            self.oLockSetup.release()
            self.oLog.fDebug('fSetup: oLockSetup Released', 5)
            
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fSetup_Meta(self):
        self.oLog.fDebug('Inside fSetup_Meta', 5)
        self.ctMClasses = {}
        

        for (iCID, strCName, strAllowMerge, strNote) in self.oDB.fSelect(self.sqlSelectClasses):
            oC = TMClass(strCName, strAllowMerge)
            for (strAttr,) in self.oDB.fSelect(self.sqlSelectClassPKs, [iCID]):
                assert strAttr in ['GUID', 'USCID']
                oC.ctValidPKs.append(strAttr)
                
            for oRow in self.oDB.fSelect(self.sqlSelectDEs, [iCID]):
                (iGID, strGName, strAllowMult, strHasTypes, strHasDepends, strNote) = oRow
                oG = TMGroup(oC, iGID, strGName, strAllowMult, strHasTypes, strHasDepends, strNote)
            
                for (iGTypeID, strGTypeName) in self.oDB.fSelect(self.sqlSelectTypes, [iGID]):
                    oG.fAddType(strGTypeName, iGTypeID)

                for (iGDepID, strGDepName) in self.oDB.fSelect(self.sqlSelectDepends, [iGID]):
                    oG.oMDepends.fAdd(strGDepName, iGDepID)

                for (iAID, strAName, strEncryptDataID, strFilter, strAutoGenFunc, strAutoGenP1) in self.oDB.fSelect(self.sqlSelectAttrs, [iGID]):
                    oA = TMAttr(oG, iAID, strAName, strEncryptDataID, strFilter, strAutoGenFunc, strAutoGenP1, self.oEncrypt)

                    for (iSORID, iGTYPEID, iWriteLevel, strReadTrans) in self.oDB.fSelect(self.sqlSelectAttrAuth, [iAID]):
                        oA.fAddAuthLevel(iSORID, iWriteLevel, strReadTrans, iGTYPEID)
                    
                    oG.fAddAttr(oA)
                
                oC.fAddGroup(oG)

            self.ctMClasses[oC.fGetKey()] = oC

        # load SOR PKs
        self.ctSORPKs = {}
        for (sSOR, sPK) in self.oDB.fSelect(self.sqlSelectSORPKs):
            self.ctSORPKs[sSOR] = sPK

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fSetup_SORs(self):
        self.oLog.fDebug('Inside fSetup_SORs', 5)
        self.ctSOR2ID = {}
        self.ctID2SOR = {}
        self.ctSORFuncAuthority = {}
        
        for (iSORID, strSORName) in self.oDB.fSelect(self.sqlSelectSORs):
            self.ctSOR2ID[strSORName] = iSORID
            self.ctID2SOR[iSORID] = strSORName

        # load SOR Authority:
        for (strSOR, strFunc) in self.oDB.fSelect(self.sqlSelectSORFuncAuthority):
            self.ctSORFuncAuthority[(strSOR, strFunc)] = 1
            
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fSetup_Util(self):
        self.oLog.fDebug('Inside fSetup_Util', 5)
        self.oSISUtil = TSISUtil(self.oLog, self.oProf)
        self.oKIMUtil = TKIMUtil(self.oLog, self.oProf)
        self.oPPBSUtil = TPPBSUtil(self.oLog, self.oProf)
    
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fSetup_Query(self):
        self.oLog.fDebug('Inside fSetup_Query', 5)
        self.oQuery = TQuery(self.oLog, self.oProf)
    
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fConnect(self, bForceConnect=0):
        self.oLog.fDebug('Inside fConnect', 5)
        # reconnect if system has been idle for more than 10 minutes:
        iCurrTime = time.time()
        if not self.oDB:
            self.oDB = DBToolsOX.TDBConnection(oInit.golden.strCatalog,
                                               oInit.golden.strUsername,
                                               oInit.golden.strPassword,
                                               self.oLog,
                                               strType = DBToolsOX.DB_TYPE_ORACLE,
                                               bDoProfiling=oInit.golden.bDoProfiling,
                                               iNumConnectTries=oInit.golden.iNumConnectTries,
                                               bAutoCommit=0)
      
            self.iLastConnect = iCurrTime

        elif (iCurrTime - self.iLastConnect > 60*1) or bForceConnect:
            self.oDB.fCommit()
            self.oDB.fConnect()
            self.oDB.oProf.fDisplayProfile()
            self.oDB.oProf.fReset()
            self.iLastConnect = iCurrTime

    #------------------------------------------------------------------------
    #
    #  Checks to see if DB is alive.
    #
    #------------------------------------------------------------------------
    def fPing(self):
        self.oLog.fDebug('Inside fPing', 5)
        self.fSetup()
        try:
            self.oLog.fDebug('fPing: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()  # start lock
            self.oLog.fDebug('fPing: oLockAdd Acquired', 5)
            
            self.fConnect()
            self.oDB.fSelect("select sysdate from dual")

        finally:
            self.oLog.fDebug('fPing: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fPing: oLockAdd Released', 5)
        
    #------------------------------------------------------------------------
    #
    #  This is how the function is called & return values used (from
    #  GoldenPR):
    #    (oPOutput, ctPErased, oIDsP) = self.oPR.fCreateoPInput, strSOR)
    #    strXML = self.strRetXML % (strAction, oIDsP.ctPKs['USCID'], strAction)
    #
    #------------------------------------------------------------------------
    def fCreate(self, oObj, strSOR):
        self.oLog.fDebug('Inside fCreate', 5)
        # check to see that there is NO USCID
        for strPK in oObj.oMClass.ctValidPKs:
            if strPK in oObj.ctPKs:
                raise ERepository(113, "Provided a USCID/GUID on a Create: %s" % (strPK))
        
        return self.fAddExplicit(oObj, strSOR)

    #------------------------------------------------------------------------
    #
    #  This is how the function is called & return values used (from
    #  GoldenPR):
    #    (oPOutput, ctPErased, oIDsP) = self.oPR.fUpdate(oPInput, strSOR)
    #    strXML = self.strRetXML % (strAction, oIDsP.ctPKs['USCID'], strAction)
    #
    #------------------------------------------------------------------------
    def fUpdate(self, oObj, strSOR):
        self.oLog.fDebug('Inside fUpdate', 5)
        # check to see that there IS a USCID
        bHasPK = 0

        for strPK in oObj.oMClass.ctValidPKs:
            if (strPK in oObj.ctPKs) and (oObj.ctPKs[strPK] is not None) and (len(oObj.ctPKs[strPK]) > 0):
                bHasPK = 1
                break

        if bHasPK == 0:
            raise ERepository(114, "Did not provide a USCID/GUID on an Update")
         
        return self.fAddExplicit(oObj, strSOR)

    #------------------------------------------------------------------------
    #
    #  Virtual, adds a record to the repository.
    #
    #------------------------------------------------------------------------
    def fAddExplicit(self, oObj, strSOR):
        self.oLog.fDebug('Inside fAddExplicit PASS', 5)
        pass

    #------------------------------------------------------------------------
    #
    #  Creates the base information for a given record.
    #
    #  oUP: object to apply to db
    #  oP:  given object by SOR
    #
    #------------------------------------------------------------------------
    def fCreateRecordShell(self, oUP, oP, strSOR, strNote = ''):
        self.oLog.fDebug('Inside fCreateRecordShell: %s' % (strSOR), 5)
        iRID = self.oDB.fSelect(self.sqlSelectNextRID % (oP.oMClass.strName))[0][0]
        oUP.iRID = iRID

        iCount = 0
        iLoopCounter = 0
        while 1:
            iLoopCounter += 1
            if iLoopCounter > 50:
                raise ERepository(210, "Internal looped too many times: fCreateRecordShell")
            

            # IN OTHER CASES:
            iIndex = 0
            ctEIDs = []
            for strPK in oP.oMClass.ctValidPKs:
                strPKValue = None
                if strPK == 'GUID':
                    strPKValue = self.fGenGUID()
                if strPK == 'USCID':
                    strPKValue = self.fGenUSCID()
                    
                # This will add to PKs container, as well as the
                # EPKs container..
                oUP.fAddPK(strPK, strPKValue, self.oEncrypt)
                ctEIDs.append(oUP.ctEPKs[strPK])
                # not needed.. ?
                iIndex += 1
                

            try:
                self.oDB.fExec(self.sqlInsertRecordShell % (oP.oMClass.strName), [iRID] + ctEIDs + ['GPR Insert [%s] %s' % (strSOR, strNote)])
                break
            
            except DBToolsOX.cx_Oracle.DatabaseError:  # used to be IntegrityError
                iCount += 1
                if iCount > oInit.golden.iInsertTries:
                    strTmp = ''.join(traceback.format_exception(sys.exc_info()[0], sys.exc_info()[1], sys.exc_info()[2]))
                    self.oLog.fError("Database Error: \n" + strTmp.strip(), 3)
                    raise ERepository(202, "Reached MAX insert tries on MasterShell")

                continue
            
        return iRID

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fGenGUID(self):
        self.oLog.fDebug('Inside fGenGUID', 5)
        binGUID = self.oDB.fSelect(self.sqlGenerateGUID)[0][0]
        strGUID = binGUID.hex()
        return strGUID

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fGenUSCID(self):
        self.oLog.fDebug('Inside fGenUSCID', 5)
        bValidUSCID = False
        iMaxNumOfLoops = 10
        while (not bValidUSCID) and iMaxNumOfLoops > 0:
            strUSCID = str(random.uniform(1000000001, 9999999999))[:10]
            if (strUSCID.find('666') < 0):
                bValidUSCID = True
            else:
                self.oLog.fDebug("fGenUSCID: Rejected USCID " + strUSCID, 5)
                iMaxNumOfLoops = iMaxNumOfLoops - 1

        return strUSCID

    #------------------------------------------------------------------------
    #
    #  Given oUP (output class w/ iRID), oP (input record), strSOR
    #  write updates appropriate record in DB.
    #
    #------------------------------------------------------------------------
    def fUpdateRecord(self, oUP, oP, strSOR):
        self.oLog.fDebug('Inside fUpdateRecord', 5)
        self.fReadRecordShell(oUP, oUP.iRID)
        (oObjErased, bChanged) = self.fUpdateRecordAGs(oUP, oP)
        if bChanged:
            self.fUpdateRecordShell(oUP, oP, strSOR)
        else:
            self.oLog.fDebug("fUpdateRecord: %d - updated with no data changes, bypassing DTM update" % oUP.iRID, 5)
        return (oObjErased, bChanged)
        
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fUpdateRecordShell(self, oUP, oP, strSOR, strNote=''):
        self.oLog.fDebug('Inside fUpdateRecordShell: %d - %s' % (oUP.iRID, strSOR), 5)
        iRID = oUP.iRID
        self.oDB.fExec(self.sqlUpdateRecordShell % (oP.oMClass.strName),
                       ['GPR Update [%s] %s' % (strSOR, strNote), iRID])
        
    #------------------------------------------------------------------------
    #
    #  Reads the shell of a person, writes results into oUP.
    #
    #  Notes:
    #    Shell has the following info:
    #      RID
    #      PKs
    #      CreateDTM
    #      ModifiedDTM
    #      IsActive
    #      Note
    #
    #------------------------------------------------------------------------
    def fReadRecordShell(self, oUP, iRID):
        self.oLog.fDebug('Inside fReadRecordShell', 5)
        oUP.iRID = iRID
        sqlSelect = self.sqlSelectRecordShell % (', '.join(oUP.oMClass.ctValidPKs),
                                                 oUP.oMClass.strName)
        ctRows = self.oDB.fSelect(sqlSelect, [iRID])
        if len(ctRows) == 0: raise ERepository(205, "Invalid RID given to fReadRecordShell: %s" % (str(iRID)))

        ctRow = list(ctRows[0])
        # The order of PKs returned should be same as
        # returned by the sql query
        for strPK in oUP.oMClass.ctValidPKs:
            oUP.fAddEPK(strPK, ctRow[0], self.oEncrypt)
            del ctRow[0]
        
        (oUP.oCreateDTM, oUP.oModifiedDTM, oUP.strIsActive, oUP.strNote) = ctRow

    #------------------------------------------------------------------------
    #
    #  Reads the historical information for a record, writes results
    #  in oUP.
    #
    #------------------------------------------------------------------------
    def fReadRecordHistory(self, oUP):
        self.oLog.fDebug('Inside fReadRecordHistory', 5)
        if oUP.oMClass.strAllowMerge != 'Y':
            return

        iRID = oUP.iRID
        strColumnNames = str(', '.join(oUP.oMClass.ctValidPKs))
        strTableName = str(oUP.oMClass.strName)
        sqlSelect = 'select ' + strColumnNames  + ' from ' + strTableName + ' p, ' + strTableName + '_merge pm where p.RID = pm.MERGED_RID and pm.final_rid = ?'
        for ctEPKs in self.oDB.fSelectDict(sqlSelect, [iRID]):
            oUP.fAddHistoricalEPKs(ctEPKs, self.oEncrypt)

    #------------------------------------------------------------------------
    #
    #  Query for attributes by taking into account:
    #    Group type
    #    Group dependencies
    #
    #  Todo:
    #    [x] Group dependencies
    #
    #  Notes:
    #    Difference between this method & fReadAG:
    #    o fReadAG reads the particular attribute we're interested
    #      in (i.e. by type/deps etc)
    #    o Here we're interested in all attributes for the RID
    #      (i.e. including all types/deps, etc)
    #
    #------------------------------------------------------------------------
    def fReadRecordMGroup(self, oP, iRID, oMGroup):
        self.oLog.fDebug('Inside fReadRecordMGroup', 5)
        ctToSelect = []
        ctDeps = []

        if oMGroup.fHasDepends():
            ctDeps = oMGroup.oMDepends.fGetKeys()

        if len(oMGroup.ctTypes) > 0:
            ctToSelect.append('GTYPE_ID')

        for strDep in ctDeps:
            ctToSelect.append(strDep)

        ctAttrs = list(oMGroup.ctMAttrs.values())
        for oMAttr in ctAttrs:
            ctToSelect.append(oMAttr.strName+'_Value')
            ctToSelect.append(oMAttr.strName+'_SOR')
            ctToSelect.append(oMAttr.strName+'_DTM')

        strToSelect = ', '.join(ctToSelect)
        sqlSelect = self.sqlSelectGroup % (strToSelect, oMGroup.oMClass.strName, oMGroup.strName)
        for ctRow in self.oDB.fSelect(sqlSelect, [iRID]):
            oAG = TAttrGroup(oMGroup)
 
            if len(oMGroup.ctTypes) > 0:
                oAG.strType = oMGroup.fTypeID2Type(ctRow[0])
                ctRow = ctRow[1:]

            if oMGroup.fHasDepends():
                # load valid deps
                self.fLoadGroupDepends(oAG, 1)
                # load given deps
                for strDep in ctDeps:
                    oAG.oDepends.fSetGivenItem(strDep, ctRow[0])
                    ctRow = ctRow[1:]

            for oMAttr in ctAttrs:
                strDBValue = ctRow[0]
                iSOR = ctRow[1]
                oDTM = ctRow[2]
                ctRow = ctRow[3:]
                    
                if iSOR is None:
                    continue
                
                oA = TAttr(oMAttr)
                oA.strDBValue = strDBValue
                oA.strSOR = self.ctID2SOR[iSOR]
                oA.oDTM = oDTM
                oA.fDecrypt()
                    
                oAG.fAddAttr(oA)
            
            oP.fAddAG(oAG)
        self.oLog.fDebug('END fReadRecordMGroup', 5)
        
    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Todo: limit attributes in group that are returned as response
    #        to a query...
    #
    #  iVIP:
    #    USCID (plus Historical IDs)
    #    Name fields
    #    Phone
    #    Email
    #    Address
    #
    #  Relevant existing attrs (in addition to name):
    #    Person.StudentInfo.ContactEmail      SIS
    #    Person.Address.Line1                 SIS-Local/Permanent/Foreign  PPBS-Home
    #    Person.Address.Line2                 SIS-Local/Permanent/Foreign  
    #    Person.Address.City                  SIS-Local/Permanent/Foreign  PPBS-Home
    #    Person.Address.State                 SIS-Local/Permanent/         PPBS-Home
    #    Person.Address.Zip                   SIS-Local/Permanent/         PPBS-Home
    #    Person.Address.Zip4                  SIS-Local/Permanent/
    #    Person.Address.Province              SIS-     /         /Foreign
    #    Person.Address.PostalCode            SIS-     /         /Foreign
    #    Person.Address.Country               SIS-Local/Permanent/Foreign
    #    Person.Address.Phone                 SIS-Local/Permanent/Foreign  PPBS-Home
    #    Person.EmployeeInfo.WorkPhone                                     PPBS
    #    Person.EmployeeInfo.WorkCell                                      PPBS
    #    Person.EmployeeInfo.PreferredEmail                                PPBS
    #
    #------------------------------------------------------------------------
    def fQueryRecord(self, iRID, oMClass, strSOR):
        self.oLog.fDebug('Inside fQueryRecord', 5)
        #
        # For now, if SOR is iVIP just return
        # everything it has read access to..
        #
        if strSOR == 'iVIP': return self.fReadRecord(iRID, oMClass)

        ctQueryFilter = self.oQuery.fGetQueryFilter()

        oP = TObject(oMClass)
        self.fReadRecordShell(oP, iRID)

        # get historical PKs..
        self.fReadRecordHistory(oP)

        # get other attrs..
        for sKey in ctQueryFilter[strSOR]:
            sAttr, sType = sKey
            if sAttr != 'PKs':
                oMGroup = oMClass.ctMGroups[(sAttr,)]
                ctAG = self.fReadAG(iRID, oMGroup, sType)
                for oAG in ctAG:
                    oAG2 = oAG.fCopyShell()
                    oAG2.iRID = oAG.iRID
                    ctAttrs = oAG.fGetAttrNames()
                    bAttrFound = 0
                    for strAttrName in ctAttrs:
                        if strAttrName in ctQueryFilter[strSOR][sKey]:
                            bAttrFound = 1
                            oAttr = oAG.ctAttrs[(strAttrName,)]
                            oAG2.fAddAttr(oAttr)
                    if bAttrFound: oP.fAddAG(oAG2)

        # don't need the GUID so remove...
        for strKey in oP.oMClass.ctValidPKs:
            if strKey not in ctQueryFilter[strSOR][('PKs', None)]:
                if strKey in oP.ctPKs:
                    del oP.ctPKs[strKey]
                for ctPKs in oP.ctHistoricalPKs:
                    if strKey in ctPKs:
                        del ctPKs[strKey]
                
        return oP

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fReadRecord(self, iRID, oMClass):
        self.oLog.fDebug('Inside fReadRecord', 5)
        oP = TObject(oMClass)
        self.fReadRecordShell(oP, iRID)
        # get historical PKs..
        self.fReadRecordHistory(oP)
        # for every DE, read it
        if (iRID is not None):
            for oMGroup in list(oMClass.ctMGroups.values()):
                self.fReadRecordMGroup(oP, iRID, oMGroup)
        else:
            self.oLog.fDebug('iRID is None', 5)
        self.oLog.fDebug('END fReadRecord', 5)
        return oP

    #------------------------------------------------------------------------
    #
    #  Given dest & source object, updates appropriate AGs
    #
    #  return:
    #    list of AGs overwritten (AG is a group).
    #
    #------------------------------------------------------------------------
    def fUpdateRecordAGs(self, oObjDest, oObjSrc):
        iRID = oObjDest.iRID
        self.oLog.fDebug('Inside fUpdateRecordAGs: %d' % (iRID), 5)
        bChanged = False
        oObjErased = oObjSrc.fCopyShell()
        
        #
        # ctAGKey: (oMGroup.Name [, Type] [, (DepKey, DepVal), ...])
        # ctAGSrc: [oAGroup, ...] since can be multi-valued
        #
        for (ctAGKey, ctAGSrc) in list(oObjSrc.ctAttrGroups.items()):
            oMGroup = oObjSrc.oMClass.ctMGroups[(ctAGKey[0],)]
            strType = None
            ctDepends = []
            if len(ctAGSrc) > 0:
                strType = ctAGSrc[0].strType
                ctDepends = ctAGSrc[0].oDepends.fGetGivenItems()
            else:
                # Hack:
                # If dependent group is also multi-valued...
                #
                # i.e. in case of attribute group with dependencies,
                # even if SOR does not provide attribute data, it
                # will still provide dependency data & we want to
                # load that..
                if oMGroup.fHasDepends():
                    ctTmp = ctAGKey[1:]
                    for ctDep in ctTmp:
                        ctDepends.append(ctDep)

            ctAGDest = self.fReadAG(iRID, oMGroup, strType, ctDepends)
            
            (ctAGInsert, ctAGUpdate, ctAGDelete, ctAGErased) = self.fCompareAGs(oMGroup, ctAGSrc, ctAGDest)

            for oAG in ctAGDelete:
                self.fDeleteAG(oAG)
                self.oLog.fDebug('  change detected on DELETE  ', 5)
                bChanged = True
            for oAG in ctAGInsert:
                oAG.iRID = iRID
                self.fInsertAG(oAG)
                self.oLog.fDebug('  change detected on INSERT  ', 5)
                bChanged = True
            for oAG in ctAGUpdate:
                self.fUpdateAG(oAG)
                self.oLog.fDebug('  change detected on UPDATE  ', 5)
                bChanged = True
            for oAG in ctAGErased:
                # Note:
                #   the erased person object will contain list of
                #   attribute groups, with only the attributes that
                #   were overwritten.
                oObjErased.fAddAG(oAG)
                self.oLog.fDebug('  change detected on ERASE   ', 5)
                bChanged = True
                
        return (oObjErased, bChanged)
            
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fInsertAG(self, oAG):
        self.oLog.fDebug('Inside fInsertAG: %s - %s' % (oAG.iRID, str(oAG.fGetKey())), 5)
        
        oMGroup = oAG.oMGroup
        ctAttrs = oAG.fGetAttrNames()  # insert only given attributes
        strCols = self.fAttrs2Cols(ctAttrs)

        strVals = ', '.join(["?, ?, sysdate"] * len(ctAttrs))

        ctVals = [oAG.iRID, oAG.strNote]
        for strAttrName in ctAttrs:
            oAttr = oAG.ctAttrs[(strAttrName,)]
            ctVals.append(oAttr.strDBValue)
            ctVals.append(self.ctSOR2ID[oAttr.strSOR])

        if oMGroup.fHasTypes():
            strCols += ", GTYPE_ID"
            strVals += ", ?"
            ctVals.append(oMGroup.fType2TypeID(oAG.strType))

        if oMGroup.fHasDepends():
            ctDeps = oMGroup.oMDepends.fGetKeys()
            for strDep in ctDeps:
                strDepCol = ", %s" % strDep
                strCols += strDepCol
                strDepVal = oAG.oDepends.fGetGivenValue(strDep)
                strVals += ", ?"
                ctVals.append(strDepVal)

        sqlInsertAG = self.sqlInsertAG % (oMGroup.oMClass.strName, oMGroup.strName, strCols, strVals)
        self.oDB.fExec(sqlInsertAG, ctVals)
        
    #------------------------------------------------------------------------
    #
    #  Updates happen at attribute level (i.e. the "update" attribute
    #  group contains only those attributes that need updating).
    #
    #------------------------------------------------------------------------
    def fUpdateAG(self, oAG):
        self.oLog.fDebug('Inside fUpdateAG: %s - %s' % (oAG.iRID, str(oAG.fGetKey())), 5)
        
        oMGroup = oAG.oMGroup
        ctAttrs = oAG.fGetAttrNames()  # update only given attributes

        strSet = ""
        ctVals = [oAG.strNote]
        for strAttrName in ctAttrs:
            oAttr = oAG.ctAttrs[(strAttrName,)]
            strSet += ",\n   %s_Value = ?, %s_SOR = ?, %s_DTM = sysdate" % (strAttrName, strAttrName, strAttrName)
            ctVals.append(oAttr.strDBValue)
            ctVals.append(self.ctSOR2ID[oAttr.strSOR])            

        ctVals.append(oAG.strID)
        sqlUpdate = self.sqlUpdateAG % (oMGroup.oMClass.strName, oMGroup.strName, strSet)
        self.oDB.fExec(sqlUpdate, ctVals)
        
    #------------------------------------------------------------------------
    #
    #  Can only delete attribute value from multi-valued attributes
    #  and those which have specifically been selected for delete
    #
    #------------------------------------------------------------------------
    def fDeleteAG(self, oAG):
        self.oLog.fDebug('Inside fDeleteAG: %s - %s' % (oAG.iRID, str(oAG.fGetKey())), 5)

        if oAG.oMGroup.strAllowMult == 'N':
            if not oAG.bOverrideAndAllowDelete:
                raise ERepository(206, "shouldn't have reached fDeleteAG")

        sqlDeleteAG = self.sqlDeleteAG % (oAG.oMGroup.oMClass.strName, oAG.oMGroup.strName)
        self.oDB.fExec(sqlDeleteAG, [oAG.strID])

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fAttrs2Cols(self, ctAttrs):
        self.oLog.fDebug('Inside fAttrs2Cols', 5)
        # can cache this for performance boost:
        ctCols = []
        for strAttr in ctAttrs:
            ctCols.append("%s_Value" % (strAttr))
            ctCols.append("%s_SOR" % (strAttr))
            ctCols.append("%s_DTM" % (strAttr))

        return ', '.join(ctCols)
           
    #------------------------------------------------------------------------
    #
    #  Get destination list of attribute groups (list is to accommodate multi-
    #  valued groups, otherwise we're dealing with just one group).
    #
    #  Get dependency info (valid & given) into the group as well.
    #
    #------------------------------------------------------------------------
    def fReadAG(self, iRID, oMGroup, strType=None, ctDepends=[]):
        self.oLog.fDebug('Inside fReadAG', 5)
        ctAGs = []
        ctAttrs = oMGroup.fGetAttrNames()
        strCols = self.fAttrs2Cols(ctAttrs)

        #
        # Get attributes by RID (and possibly by type and/or dependencies)
        #
        sqlSelect = self.sqlSelectAG % (strCols, oMGroup.oMClass.strName, oMGroup.strName)
        sqlArgs = [iRID]

        ctRows = None

        sqlDepCondition = ""
        sqlDepArgs = []
        if oMGroup.fHasDepends():
            # get all dependencies & format query accordingly..
            for strDepName, strDepValue in ctDepends:
                sqlDepCondition += "and %s = ?" % strDepName
                sqlDepArgs.append(strDepValue)
                                                                                                   
        if oMGroup.fHasTypes():
            sqlSelect += "and GTYPE_ID = ?"
            iTypeID = oMGroup.fType2TypeID(strType)
            sqlArgs.append(iTypeID)
            
            sqlSelect += sqlDepCondition
            sqlArgs.extend(sqlDepArgs)

            #ctRows = self.oDB.fSelect(sqlSelect, [iRID, iTypeID])
            ctRows = self.oDB.fSelect(sqlSelect, sqlArgs)
            
        else:
            sqlSelect += sqlDepCondition
            sqlArgs.extend(sqlDepArgs)

            #ctRows = self.oDB.fSelect(sqlSelect, [iRID])
            ctRows = self.oDB.fSelect(sqlSelect, sqlArgs)

        for ctRow in ctRows:
            oAG = TAttrGroup(oMGroup)
            oAG.iRID = ctRow[0]
            oAG.oCreateDTM = ctRow[1]
            oAG.oModifiedDTM = ctRow[2]
            oAG.strNote = ctRow[3]
            oAG.strID = ctRow[4]
            ctRow = ctRow[5:]

            if strType:
                oAG.strType = strType

            #
            # Add dependencies:
            #   1) load valid dependencies
            #   2) add given dependencies
            #
            if len(ctDepends):
                self.fLoadGroupDepends(oAG)
                for strDepName, strDepValue in ctDepends:
                    oAG.oDepends.fSetGivenItem(strDepName, strDepValue)
            
            for strAttrName in ctAttrs:
                oMAttr = oMGroup.ctMAttrs[(strAttrName,)]
                oA = TAttr(oMAttr)
                oA.strDBValue = ctRow[0]
                iSORID = ctRow[1]
                oDTM = ctRow[2]
                ctRow = ctRow[3:]
                if oA.strDBValue:
                    if iSORID not in self.ctID2SOR:
                        raise ERepository(207, 'FOUND Value in DB WITHOUT SOR: %s' % (str(iSORID)))
                    
                    oA.strSOR = self.ctID2SOR[iSORID]
                    oA.oDTM = oDTM
                    oA.fDecrypt()
                    oAG.fAddAttr(oA)

            ctAGs.append(oAG)
            
        return ctAGs

    #------------------------------------------------------------------------
    #
    #  Compares two AG values
    #
    #------------------------------------------------------------------------
    def fCompareAGs(self, oMGroup, ctAGSrc, ctAGDest):
        self.oLog.fDebug('Inside fCompareAGs: %s' % (oMGroup.strName), 5)

        ctI = []   # inserts
        ctU = []   # updates
        ctD = []   # deletes
        ctE = []   # old values that were erased

        # for multi-valued groups:
        if oMGroup.strAllowMult == 'Y':
            #
            # check for the difference
            #
            # Note: 1) For multi-valued attributes, if the SOR attributes match
            #       existing attributes, the existing attributes do not need
            #       to be updated, and we will no longer apply it simply
            #       for the sake of updating the DTM
            #       2) Any new data gets added.
            #       3) If SOR data does not match existing attributes, then the
            #       existing attributes need to be deleted.
            #
            for oAGSrc in ctAGSrc:
                bFoundMatch = 0
                for oAGDest in ctAGDest:
                    if oAGSrc.fIsSame(oAGDest):
                        # Formerly would append to update list
                        # now we don't want to do this because
                        # we want to ignore updates which are identical.
                        #ctU.append(oAGDest)
                        ctAGDest.remove(oAGDest)
                        bFoundMatch = 1
                        break
                    
                if bFoundMatch:
                    continue

                # if not there, or not the same, insert
                ctI.append(oAGSrc)

            #
            # delete the rest:
            # (since the remaining objects in ctAGDest
            # were not found in data from SOR)
            #
            ctD = ctAGDest
            ctE = ctAGDest
            
        else: #oMGroup.strAllowMult == 'N':
            if len(ctAGSrc) > 1 or len(ctAGDest) > 1:
                raise ERepository(108, "Received multi value when single value expected")

            #
            # Check: since record shell is created even on a Create,
            #        will we ever insert?
            #

            # insert on zero:
            if len(ctAGDest) == 0:
                oAGSrc = ctAGSrc[0]
                oAGDest = TAttrGroup(oMGroup)

                #oAGU = TAttrGroup(oMGroup)
                #oAGU.strType = oAGSrc.strType
                #
                # the following should accomplish the above
                # plus loading depends info
                oAGU = oAGSrc.fCopyShell()


                if oDeleteFilter.fCheckAttrGroupForDelete(oAGSrc):
                    self.oLog.fDebug("fCompareAGs: Ignoring attribute group for insert due to delete filter: \n%s" %(oAGU), 5)
                    #ctD.append(oAGSrc)
                else:
                    (oAGU, oAGErased) = self.fFilterAG(oAGU, oAGSrc, oAGDest)
                    if oAGU:
                        ctI.append(oAGU)

                    if oAGErased:
                        ctE.append(oAGErased)


            # update on one:
            else:
                oAGSrc = ctAGSrc[0]
                oAGDest = ctAGDest[0]

                #oAGU = TAttrGroup(oMGroup)
                #oAGU.iRID = oAGDest.iRID
                #oAGU.strID = oAGDest.strID
                #oAGU.strType = oAGDest.strType
                #oAGU.strNote = oAGSrc.strNote
                #
                # following code accomplishes:
                # - oAGU = TAttrGroup(oMGroup)
                # - oAGU.strType = oAGDest.strType
                # - oAGU.oDepends = TDepends()
                # - oAGU.oDepends = oAGU.oDepends.fUpdateShell(oAGU.oDepends)
                oAGU = oAGDest.fCopyShell()
                oAGU.iRID = oAGDest.iRID
                oAGU.strID = oAGDest.strID
                oAGU.strNote = oAGSrc.strNote
                
                if oDeleteFilter.fCheckAttrGroupForDelete(oAGSrc):
                    self.oLog.fDebug("fCompareAGs: Marking attribute group for deletion: \n%s" %(oAGDest), 5)
                    oAGDest.bOverrideAndAllowDelete = True
                    ctD.append(oAGDest)
                    ctE.append(oAGDest)
                else:
                    (oAGU, oAGErased) = self.fFilterAG(oAGU, oAGSrc, oAGDest)
                    if oAGU:
                        ctU.append(oAGU)

                    if oAGErased:
                        ctE.append(oAGErased)

            
        return (ctI, ctU, ctD, ctE)

    #------------------------------------------------------------------------
    #
    #  Given Src & Dest AttrGroup, identify data to be overwritten
    #
    #    oAGU: input, values to be overwritten
    #    oAGSrc: input: source data  (what will overwrite)
    #    oAGDest: input: destination data (what will be overwitten)
    #    return value: (oAG of attributes to update, oAG of attributes
    #                   overwritten)
    #
    #------------------------------------------------------------------------
    def fFilterAG(self, oAGU, oAGSrc, oAGDest):
        self.oLog.fDebug('Inside fFilterAG', 5)
        # make sure to update only different VALUES or SORS
        self.oLog.fDebug("Given:\noAGU: %s\noAGSrc: %s\noAGDest: %s" % (oAGU, oAGSrc, oAGDest), 5)

        # create copy attribute group for erased values
        oAGErased = oAGU.fCopyShell()

        iTypeID = oAGSrc.strType
        if iTypeID:
            iTypeID = oAGSrc.oMGroup.fType2TypeID(iTypeID)
            
        for strAttrName in oAGSrc.fGetAttrNames():
            ctAttrKey = (strAttrName,)
            # following cannot happen...
            if ctAttrKey not in oAGSrc.ctAttrs:
                continue
            oAttrSrc = oAGSrc.ctAttrs[ctAttrKey]
            
            oAttrU = None
            oAttrDest = oAttrSrc.fCopyShell()

            #
            # If dest has no such attribute,
            # only pass source to fFilterAttr
            #
            if ctAttrKey not in oAGDest.ctAttrs:
                oAttrU = self.fFilterAttr(iTypeID, oAttrSrc)

            #
            # If dest does have, pass both to fFilterAttr
            #
            else:
                oAttrDest = oAGDest.ctAttrs[ctAttrKey]
                oAttrU = self.fFilterAttr(iTypeID, oAttrSrc, oAttrDest)
                
            if oAttrU:
                # self.oLog.fDebug("fFilterAG: AttrChanged - %s" % (oAttrU.oMAttr.strName), 5)
                oAGU.fAddAttr(oAttrSrc)
                # erase values that changed:
                if oAttrU.strValue != oAttrDest.strValue:
                    oAGErased.fAddAttr(oAttrDest)

        # Only perform update if actual attributes changed:
        if not oAGU.fVerify():
            oAGU = None
        if not oAGErased.fVerify():
            oAGErased = None

        self.oLog.fDebug("Results:\noAGU: %s\noAGErased: %s" % (oAGU, oAGErased), 5)
        return (oAGU, oAGErased)
        
    #------------------------------------------------------------------------
    #
    #  Compares two attributes to see if should perform an update
    #  return value: oAttr if it should be written, None if not.
    #
    #------------------------------------------------------------------------
    def fFilterAttr(self, iGType, oAttrSrc, oAttrDest=None):
        self.oLog.fDebug('Inside fFilterAttr: SRC: [%s]  DST: [%s]' % (str(oAttrSrc), str(oAttrDest)), 5)

        # make sure even authorized!!
        iAttrLevelSrc = oAttrSrc.oMAttr.fGetAuthLevel(self.ctSOR2ID[oAttrSrc.strSOR], iGType)[0]

        # if Admin, ALWAYS overwrite!
        if oAttrSrc.strSOR in ['ADMIN']:
            self.oLog.fDebug('  ADMIN, overwrites.', 5)
            return oAttrSrc

        if (iAttrLevelSrc is None) or (iAttrLevelSrc <= 0):
            raise ERepository(109, "%s attempted to write to the attribute (%s) w/o Authority level" % (oAttrSrc.strSOR, oAttrSrc.oMAttr.strName))
        
        # if no dest, and source is empty string:
        if not oAttrDest and oAttrSrc.strDBValue == "":
            # special case where we are no longer fudging encryption and
            # we have an empty string (which Oracle treats as null instead of setting
            # an actual empty string value).
            # self.oLog.fDebug("fFilterAttr: no DEST attr - %s - and source string is empty" % (oAttrSrc.oMAttr.strName), 5)
            # self.oLog.fDebug('  No Dest, empty source', 5)
            # self.oLog.fDebug('  values are considered the same, do not overwrite  ', 5)
            return None
        
        # if no dest, use source:
        if not oAttrDest:
            # self.oLog.fDebug("fFilterAttr: no DEST attr - %s" % (oAttrSrc.oMAttr.strName), 5)
            # self.oLog.fDebug('  No Dest, write.', 5)
            return oAttrSrc
        
        # always overwrite, since we know at least DTM may change, if not Value or SOR:

        # check AuthLevel:
        iAttrLevelDest = oAttrDest.oMAttr.fGetAuthLevel(self.ctSOR2ID[oAttrDest.strSOR], iGType)[0]
        if iAttrLevelDest is None:  # must have been Admin:
            if oAttrDest.strSOR not in ['ADMIN']:
                raise ERepository(201, 'SOR %s with no Auth Level in DB.' % (oAttrDest.strSOR))

            # self.oLog.fDebug('Last person to write was ADMIN, overwrite.', 5)
            return oAttrSrc         # anyone can overwrite Admin

        # if greater auth level, can always overwrite:
        if iAttrLevelSrc > iAttrLevelDest:
            # self.oLog.fDebug("fFilterAttr: authorized to overwrite - %s" % (oAttrSrc.oMAttr.strName), 5)
            # self.oLog.fDebug('  greater auth level, overwrite.', 5)
            return oAttrSrc

        # if same, need to check DTM:
        if iAttrLevelSrc == iAttrLevelDest:
            # if there isn't a DTM, it means that it's NOW, i.e. LATEST:
            if oAttrSrc.oDTM is None:
                # Check if the data is the same.  If it is do not update since
                # only the DTM will be updated.
                if oAttrSrc.fIsSame(oAttrDest):
                    self.oLog.fDebug('src: %s (%s), dest %s (%s), src==dst %s'  % \
                                     (str(oAttrSrc.oDTM), str(oAttrSrc.strValue),
                                      str(oAttrDest.oDTM), str(oAttrDest.strValue),
                                      str(oAttrSrc.strValue == oAttrDest.strValue)), 5)
                    self.oLog.fDebug('  values are the same, do not overwrite  ', 5)
                    return None
                self.oLog.fDebug('  same auth level, src has no DTM, different values, overwrite.', 5)
                return oAttrSrc

            # there should be a DTM for every attribute in DB:
            if oAttrDest.oDTM is None:
                raise ERepository(209, "Attribute in DB has no DTM stamp: %s" % (oAttrSrc.oMAttr.strName))

            # overwrite only when SRC is Newer than Dest:
            self.oLog.fDebug('src: %s (%s), dest %s (%s), src>dst %s'  % \
                             (str(oAttrSrc.oDTM), str(oAttrSrc.strValue),
                              str(oAttrDest.oDTM), str(oAttrDest.strValue),
                              str(oAttrSrc.oDTM > oAttrDest.oDTM)), 5)
            if oAttrSrc.oDTM > oAttrDest.oDTM:
                self.oLog.fDebug('  same auth, src has greater DTM, overwrite', 5)
                return oAttrSrc

        # there is nothing to update:
        return None

    #------------------------------------------------------------------------
    #
    #  Sets the active status for a record
    #
    #------------------------------------------------------------------------
    def fSetActiveFlag(self, oP, strActiveFlag):
        self.oLog.fDebug('Inside fSetActiveFlag', 5)
        assert strActiveFlag in ['Y', 'N'], "Invalid active flag."
        assert oP.iRID is not None, "Invalid RID"
        sqlUpdate = self.sqlUpdateActiveFlag % (oP.oMClass.strName)
        self.oDB.fExec(sqlUpdate, [strActiveFlag, oP.iRID])
        
    #------------------------------------------------------------------------
    #
    #  Clears the record's data, leaving only shell
    #
    #------------------------------------------------------------------------
    def fClearRecordData(self, oP):
        self.oLog.fDebug('Inside fClearRecordData', 5)
        assert oP.iRID is not None, "Invalid RID"
        ctClassKey = oP.oMClass.fGetKey()
        for (strAG,) in list(self.ctMClasses[ctClassKey].ctMGroups.keys()):
            strTableName = "%s_%s" % (oP.oMClass.strName, strAG)
            sqlDelete = self.sqlDeleteRecordData % (strTableName)
            self.oDB.fExec(sqlDelete, [oP.iRID])

    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Multi-threaded version of match finder
    #
    #  Holds on to RIDs until done
    #
    #  New 07-31-2006:
    #    Argument SOR needed to avoid intra-SOR merges in the PR
    #
    #  New 10-26-2006:
    #    Add keyword dictionary as params to make this function more
    #    flexible
    #
    #------------------------------------------------------------------------
    def fGetMatchesMT(self, oP, strSOR, **kw):
        self.oLog.fDebug('Inside fGetMatchesMT', 5)
        iCount = 0
        try:
            # keep trying:
            iLoopCounter = 0
            while 1:
                iLoopCounter += 1
                if iLoopCounter > 50:
                    raise ERepository(210, "Internal looped too many times: fGetMatchesMT")

                #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
                #
                # get matches:
                #
                # NOTE: fGetMatches is overridden in GPR
                #       Returned RIDs are records that matched on:
                #           PKs
                #           GR info
                #
                # ctMatches: list of RIDs
                #
                ctMatches = []
                if kw.get('bException'):
                    ctMatches = self.fGetMatches_Exception(oP, strSOR, **kw)
                else: # default matching
                    ctMatches = self.fGetMatches(oP, strSOR)

                self.oLog.fDebug('fGetMatchesMT: oLockMatches Before Acquire', 5)
                self.oLockMatches.acquire()
                iCount += 1
                self.oLog.fDebug('fGetMatchesMT: oLockMatches Acquired', 5)
                bFoundHold = 0
                # for each match:
                for iRID in ctMatches:
                    # check if it's on hold, if so, sleep for a bit and continue
                    if iRID in self.ctRIDsOnHold:
                        bFoundHold = 1
                        break

                if bFoundHold:
                    self.oLog.fDebug('[%s] Found HOLD on matches: %s' % (Logger.fGetLogTime(), str(ctMatches)), 5)
                    time.sleep(0.2)
                    self.oLog.fDebug('fGetMatchesMT: oLockMatches Before Release', 5)
                    if (iCount > 0 ):
                        self.oLockMatches.release()
                        iCount -= 1
                    self.oLog.fDebug('fGetMatchesMT: oLockMatches Released', 5)
                    continue

                # if not, put all on hold and return matches
                for iRID in ctMatches:
                    self.ctRIDsOnHold[iRID] = 1

                self.oLog.fDebug('fGetMatchesMT: oLockMatches Before Release', 5)
                if (iCount > 0 ):
                    self.oLockMatches.release()
                    iCount -= 1
                self.oLog.fDebug('fGetMatchesMT: oLockMatches Released', 5)
                return ctMatches

        except ERepository as oErr:
            raise oErr

        finally:
            self.oLog.fDebug('fGetMatchesMT: oLockMatches Before Release', 5)
            if (iCount > 0 ):
                self.oLockMatches.release()
                iCount -= 1
            self.oLog.fDebug('fGetMatchesMT: oLockMatches Released', 5)


    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fReleaseMatchesMT(self, ctMatches):
        self.oLog.fDebug('Inside fReleaseMatchesMT', 5)
        self.oLog.fDebug('fReleaseMathesMT: oLockMatches Before Acquire', 5)
        self.oLockMatches.acquire()
        self.oLog.fDebug('fReleaseMathesMT: oLockMatches Acquired', 5)
        
        # for every match:
        for iRID in ctMatches:
            # release from hold
            del self.ctRIDsOnHold[iRID]

        self.oLog.fDebug('fReleaseMathesMT: oLockMatches Before Release', 5)
        self.oLockMatches.release()
        self.oLog.fDebug('fReleaseMathesMT: oLockMatches Released', 5)

    #------------------------------------------------------------------------
    #
    #  Overridden in GPR
    #
    #  This method finds matches based on primary keys.
    #
    #  Return: list of RIDs
    #
    #  Notes:
    #  ====================================
    #  - Gets RIDs & active flag for records that match based on the PKs.
    #  - Should return only one record ?
    #  - Go through returned RIDs, if inactive then get & replace with
    #    the associated active RID (final RID)
    #
    #  New 07-31-2006:
    #    - Argument SOR needed to avoid intra-SOR merges in the PR
    #    - If no PK (e.g. Create), then no matches will be
    #      returned here; could still result in GR match later - if
    #      these latter matches are filtered out due to same SOR,
    #      then will result in insert
    #    - If there is PK, should result in one match: match by
    #      PK means the same record
    #
    #------------------------------------------------------------------------
    def fGetMatches(self, oP, strSOR):
        self.oLog.fDebug('Inside TORInterface.fGetMatches (OR): %s' % (str(oP)), 5)
        ctMatches = []

        ctIDs = []
        ctValues = []
        # generate SQL:
        for (strPK, strValue) in list(oP.ctEPKs.items()):
            ctIDs.append('%s = ?' % (strPK))
            ctValues.append(strValue)

        # if PKs were provided:
        if len(ctIDs) > 0:
            # select for those PKS:
            sqlSelect = self.sqlSelectMatchesPKs % (oP.oMClass.strName, ' or '.join(ctIDs))
            ctRes = self.oDB.fSelect(sqlSelect, ctValues)

            # if nothing returned, bad IDs:
            if len(ctRes) == 0:
                strKey = list(oP.ctPKs.keys())[0]
                strVal = oP.ctPKs[strKey]
                self.oLog.fDebug('fGetMatches: Invalid USCID specified', 5)
                raise ERepository(110, "Invalid %s: %s" % (strKey, strVal))

            # check each returned ID individually for active flag, etc:
            for (iRID, strIsActive) in ctRes:
                # if inactive record, check to see if it has been merged:
                if strIsActive == 'N':
                    ctResMerges = []
                    if oP.oMClass.strAllowMerge == 'Y':
                        ctResMerges = self.oDB.fSelect(self.sqlSelectMergedFinalID % (oP.oMClass.strName), [iRID])
                    if len(ctResMerges) == 0:
                        raise ERepository(121, "SOR provided a USCID/GUID belonging to inactive, non-merged record: %s" % (str(list(oP.ctPKs.items()))))
                    iRID = ctResMerges[0][0]

                # avoid having duplicates in return list:
                if iRID not in ctMatches:
                    ctMatches.append(iRID)

        #
        # List should be one of the following:
        # - Empty list: in case of SOR Create, there should be no
        #   matches
        # - List with only one element: in case of SOR Update, the
        #   provided PK (USCID) should generate only one match
        #
        # As a result of the above scenarios, there should be no
        # need for filtering out matches, to avoid same-SOR merges
        # down the line (since never expect to have more than 1 match)
        #

        return ctMatches

    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Handle special case matching here..
    # 
    #------------------------------------------------------------------------
    def fGetMatches_Exception(self, oP, strSOR, **kw):
        self.oLog.fDebug('Inside TORInterface.fGetMatches_Exception (OR): %s' % (str(oP)), 5)

        strReqType = kw.get('strReqType')
        if (strReqType is None) or (strReqType not in ['Query', 'GetActiveUSCID']):
            raise ERepository(212, "Received invalid request for special-case matching: %s" % (strReqType))

        ctMatches = TORInterface.fGetMatches(self, oP, strSOR)
                
        if strReqType == 'Query':
            ctQueryMatches = []
            ctQueryMatches = self.oQuery.fGetMatches(oP, ctMatches,
                                                     strSOR, self.oDB,
                                                     **kw)
            ctMatches = ctQueryMatches[:]
        elif strReqType == 'GetActiveUSCID':
            ctQueryMatches = []
            ctQueryMatches = self.oQuery.fGetActiveUSCID(oP, ctMatches,
                                                         strSOR, self.oDB,
                                                         self.ctSORPKs, **kw)
            ctMatches = ctQueryMatches[:]
                    
        return ctMatches

    #------------------------------------------------------------------------
    #
    #  For the given Attribute Group, we load dependencies (valid, as
    #  opposed to given).
    #
    #  1) Check if group has dependencies, stop if no
    #  2) Get dependency keys from the group metadata object
    #  3) For each dependency key, get the table/column pointed to (if any)
    #  4) Using the table/column get the valid values for the key
    #  5) Load the key/values into Attribute Group's Dependency object
    #
    #------------------------------------------------------------------------
    def fLoadGroupDepends(self, oAG, bUseCache=0):
        self.oLog.fDebug('Inside fLoadGroupDepends', 5)
        if oAG.oMGroup.fHasDepends():
            iGroupID = oAG.oMGroup.iGroupID
            oToday = datetime.datetime.today().date()

            for strDepName, iDepID in oAG.oMGroup.oMDepends.fGetItems():

                bCanUseCache = False
                ctCacheKey = (iGroupID, strDepName)

                if bUseCache:
                    if ctCacheKey in self.ctGroupDependsCache:
                        oLastUpd = self.ctGroupDependsCache[ctCacheKey][0]
                        if oLastUpd == oToday:
                            bCanUseCache = True

                if bCanUseCache:
                    ctValidValues = self.ctGroupDependsCache[ctCacheKey][1]
                    strFilter = self.ctGroupDependsCache[ctCacheKey][2]
                else:
                    (strDepTable, strDepCol, strFilter) = self.oDB.fSelect(self.sqlSelectDependsMetaInfo, [iDepID, iGroupID])[0]
                    ctValidValues = []
                    if strDepTable and strDepCol:
                        for (strDepValue,) in self.oDB.fSelect(self.sqlSelectDependsValidValues % (strDepCol, strDepTable)):
                            ctValidValues.append(strDepValue)
                    # update cache
                    self.ctGroupDependsCache[ctCacheKey] = (oToday, ctValidValues, strFilter)

                if not strFilter:
                    strFilter = None
                    
                if len(ctValidValues) == 0:
                    oAG.oDepends.fSetValidItem(strDepName, strFilter=strFilter)
                else:
                    oAG.oDepends.fSetValidItem(strDepName, ctValidValues, strFilter=strFilter)
        #return oAG




    #
    #
    #<<<<<<<<<<<<<<<<<<<<<<<<<<  XML Section  >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #
    #



    #------------------------------------------------------------------------
    #
    #  XML parsing utils
    #
    #  Notes:
    #  ====================================
    #  - We're only interested in extracting USCID(s) for the following
    #    actions:
    #            Merge
    #            DoNotMerge
    #            Unmerge
    #            SetAsActiveUSCID
    #  - We get the person node for the following actions:
    #            GetActiveUSCID
    #            Read
    #    although all they should have is the USCID.
    #  - We get the person node for the following actions:
    #            Create
    #            Update
    #    with whatever attributes are supplied. When changes are made to
    #    metadata, esp at the group-level, then parsing for these actions
    #    may be affected (i.e. review the code).
    #
    #------------------------------------------------------------------------
    def fXMLParse(self, strXML, strSOR):
        self.oLog.fDebug('Inside fXMLParse - Incoming XML: %s' % (strXML), 5)
        self.fSetup()
        if strSOR not in self.ctSOR2ID:
            raise ERepository(117, "Given SOR is not valid: %s" % (strSOR))
            
        #
        # In the following the list of (valid) actions is not used in
        # the called function, so can disregard.
        #
        ctValidActions = ['Create',
                          'Update',
                          'Merge',
                          'DoNotMerge',
                          'Unmerge',
                          'SetAsActiveUSCID',
                          'Read',
                          'GetActiveUSCID',
                          'Ping']

        strAction, oNode = self.fXMLGetAction(strXML, strSOR, ctValidActions)
        self.oLog.fDebug('Inside fXMLParse after call to get action: %s' % (strAction), 5)

        ctAuthKey = (strSOR, strAction)
        if (ctAuthKey not in self.ctSORFuncAuthority) and (strSOR != 'ADMIN'):
            self.oLog.fDebug('SOR (%s) does not have permission to call action (%s)' % (strSOR, strAction), 5)
            raise ERepository(118, '%s has no permission for given XML function: %s' % (strSOR, strAction), 'ERR', strAction)

        if strAction == 'UpdateTable':
            _ctValidNonPersonObjects = ['TermTable','RolesTable','DeptTable','MajorTable']
            strRootObject = self._fXMLGetRootObject(oNode)
            if strRootObject not in _ctValidNonPersonObjects:
                raise ERepository(127, "Table %s cannot be updated by SORs" % strRootObject)
            oObjectNode = self.fXMLGetSNs(oNode, strRootObject)[0]
            return strAction, (strRootObject, oObjectNode)
                
        if strAction == 'GetCurrentTerm':
            return strAction, None

        if strAction in ['Create', 'Read', 'GetActiveUSCID']:
            oPersonNode = self.fXMLGetSNs(oNode, 'Person')[0]
            oP = self.fXMLGetPerson(oPersonNode, strSOR)
            return strAction, (oP,)

        #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:PREPROC >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        if strAction == 'Update':
            oPersonNode = self.fXMLGetSNs(oNode, 'Person')[0]

            #
            # Pass along info needed for determining if an attribute
            # group should be bypassed if it contains bad data
            #
            ctBypassInfo = (strAction, strXML)
            oP = self.fXMLGetPerson(oPersonNode, strSOR, ctBypassInfo=ctBypassInfo)

            return strAction, (oP,)


        #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        if strAction == 'Query':
            bCreateOnNoMatch = 0
            bMatchExact = 0
            bMatchPartial = 0

            oMatchNode = self.fXMLGetSNs(oNode, 'Match', 0, 1)
            if len(oMatchNode) == 1:
                for childNode in oMatchNode[0].childNodes:
                    if childNode.nodeName == '#text':
                        continue
                    if childNode.nodeName == "Partial" and childNode.hasChildNodes():
                        bMatchPartial = int(childNode.firstChild.nodeValue)
                    if childNode.nodeName == "Exact" and childNode.hasChildNodes():
                        bMatchExact = int(childNode.firstChild.nodeValue)

            oPersonNode = self.fXMLGetSNs(oNode, 'Person')[0]
            oP = self.fXMLGetPerson(oPersonNode, strSOR)
            return strAction, (oP, dict(bCreateOnNoMatch=bCreateOnNoMatch,
                                        bMatchExact=bMatchExact,
                                        bMatchPartial=bMatchPartial))

        if strAction == 'ManualCreate':
            """
            For this action, only ADMIN is authorized (to send the request),
            but all db work should be done using the actual SOR (not ADMIN)
            """
            oActualSOR = self.fXMLGetSNs(oNode, 'ActingOnBehalfOf')[0]
            strActualSOR = str(oActualSOR.childNodes[0].nodeValue)
            oPersonNode = self.fXMLGetSNs(oNode, 'Person')[0]
            oP = self.fXMLGetPerson(oPersonNode, strActualSOR)
            return strAction, (oP, strActualSOR)

        if strAction == 'Merge':
            return strAction, self.fXMLGetMerge(oNode)

        if strAction == 'DoNotMerge':
            return strAction, self.fXMLGetDoNotMerge(oNode)
 
        if strAction == 'Unmerge':  # same params as DoNotMerge
            return strAction, self.fXMLGetDoNotMerge(oNode)

        if strAction == 'SetAsActiveUSCID':
            return strAction, self.fXMLGetSetAsActiveUSCID(oNode)

        if strAction == 'Ping':
            return strAction, None

        raise ERepository(112, "An invalid XML function (Create, Update, etc.) was provided: %s" % (strAction))

    #------------------------------------------------------------------------
    #
    #  Determine root object node
    #
    #  Should be either "Person" or something else (e.g. "TermTable")
    #
    #------------------------------------------------------------------------
    def _fXMLGetRootObject(self, oNode):
        self.oLog.fDebug('Inside fXMLGetRootObject', 5)
        strRoot = ''

        for oChild in oNode.childNodes:
            if oChild.nodeName == '#text':
                continue
            strRoot = oChild.nodeName

        return strRoot

    #------------------------------------------------------------------------
    #
    #  Given XML, returns specified Action to take
    #
    #------------------------------------------------------------------------
    def fXMLGetAction(self, strXML, strSOR, ctValidActions):
        self.oLog.fDebug('Inside fXMLGetAction', 5)
        self.fSetup()
        hXMLFile = io.StringIO(strXML)
        oNode = xml.dom.minidom.parse(hXMLFile)

        oAction = None
        for oSubNode in oNode.childNodes:
            if not oAction:
                oAction = oSubNode
            else:
                raise ERepository(120, 'Must specify one and only one action in XML (Create, Update, etc.)')
        if not oAction:
            raise ERepository(120, 'Must specify one and only one action in XML (Create, Update, etc.)')
        
        return (oAction.nodeName, oAction)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fXMLGetDoNotMerge(self, oNode):
        self.oLog.fDebug('Inside fXMLGetDoNotMerge', 5)
        strUSCIDKeep = self.fXMLGetText(self.fXMLGetSNs(oNode, 'USCID1')[0])
        strUSCIDDiscard = self.fXMLGetText(self.fXMLGetSNs(oNode, 'USCID2')[0])
        return (strUSCIDKeep, strUSCIDDiscard)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fXMLGetMerge(self, oNode):
        self.oLog.fDebug('Inside fXMLGetMerge', 5)
        strUSCIDKeep = self.fXMLGetText(self.fXMLGetSNs(oNode, 'USCIDKeep')[0])
        strUSCIDDiscard = self.fXMLGetText(self.fXMLGetSNs(oNode, 'USCIDDiscard')[0])
        return (strUSCIDKeep, strUSCIDDiscard)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fXMLGetSetAsActiveUSCID(self, oNode):
        self.oLog.fDebug('Inside fXMLGetSetAsActiveUSCID', 5)
        strUSCID = self.fXMLGetText(self.fXMLGetSNs(oNode, 'USCID')[0])
        return (strUSCID,)

    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:PREPROC >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Given a person node, build a person object
    #
    #------------------------------------------------------------------------
    def fXMLGetPerson(self, oNode, strSOR, **kw):
        self.oLog.fDebug('Inside fXMLGetPerson', 5)
        #
        # get person class metadata that we already setup
        #
        oMClass = self.ctMClasses[('Person',)]

        #
        # use that to get our person object
        #
        oP = TObject(oMClass)

        #
        # populate person object with attribute groups
        #
        for oSubNode in oNode.childNodes:
            strNodeName = oSubNode.nodeName
            if strNodeName == '#text':
                continue

            #
            # If node found in group metadata, add the node to person
            # object.
            #
            # NOTE: we only expect single-valued nodes here
            #
            oMGroup = oMClass.ctMGroups.get((strNodeName,), None)
            if oMGroup:
                # Check for groups that need special processing
                if strNodeName == 'Roles':
                    strWriteTrans = 'fProcessRolesAttrs'
                elif strNodeName == 'EmployeeInfo':
                    strWriteTrans = 'fProcessEmployeeInfoAttrs'
                else:
                    strWriteTrans = None
                oG = self.fXMLGetDE(oSubNode, oP, oMGroup, strSOR, strWriteTrans)
                if oG:
                    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:PREPROC >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
                    try:
                        oP.fAddAG(oG)
                    except ERepository as oErr:
                        strCode = str(oErr)[8:11]
                        ctBypassInfo = kw.get('ctBypassInfo')
                        if ctBypassInfo and isinstance(ctBypassInfo, tuple):
                            strAction, strRequest = ctBypassInfo
                            strName = oG.oMGroup.strName
                            bBypassBadAG = oPreProc.oAGProc.fBypassBadData( (strName, strSOR, strAction, strCode) )
                        else:
                            bBypassBadAG = False
                        if bBypassBadAG:
#                            self.oProf.fStartProfile('LOGS')
                            strTmp = ''.join(traceback.format_exception(sys.exc_info()[0], sys.exc_info()[1], sys.exc_info()[2]))
                            strTrace = strTmp.strip()
                            strTime = Logger.fGetLogTime()
                            strMsg = "[%s] [error] %s %s %s\nTRACE:\n%s\nREQUEST:\n%s\n\n" % \
                                     (strTime, strSOR, strAction, str(oErr),
                                      Logger.fPadLeft(strTrace), Logger.fPadLeft(strRequest))
                            oPreProc.oLog.fDebug(strMsg)
#                            self.oProf.fStopProfile('LOGS')
                        else:
                            raise oErr
                continue

            #
            # if we get here we know it's not single-valued, so check
            # if it's multi-valued
            #
            if strNodeName[:6] == 'Multi-':
                strGroupName = strNodeName[6:]
                
                oMGroup = oMClass.ctMGroups.get((strGroupName,), None)
                
                #
                # similar to above, check if found in group metdata
                #
                if oMGroup:
                    #
                    # make sure to only allow multiple values when
                    # permitted:
                    #
                    if oMGroup.strAllowMult == 'N':
                        raise ERepository(108, 'Received multi value when single value expected: %s' % (strNodeName))
                    #
                    # note: this initializes a list (which fAddAG
                    # already takes care of)
                    #
                    # update: need this for "empty" multi-val container ??
                    #

                    # check dependencies
                    if not oMGroup.fHasDepends():
                        oP.fAddMultiVal(oMGroup)

                    #
                    # Check for one and only one BusinessTitle of type
                    # Primary when BusinessTitles are specified.
                    #
                    if strNodeName == 'Multi-BusinessTitle':
                        if self.fInvalidBusinessTitleGroup(oSubNode, strGroupName):
                            continue

                    for oSubSubNode in oSubNode.childNodes:
                        if oSubSubNode.nodeName != strGroupName:
                            #
                            # could catch errors here
                            #
                            continue
                        
                        #
                        # DE = data element = group
                        #
                        oG = self.fXMLGetDE(oSubSubNode, oP, oMGroup, strSOR, None)
                        if oG:
                            if len(oG.ctAttrs) > 0:
                                #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:PREPROC >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
                                try:
                                    oP.fAddAG(oG)
                                except ERepository as oErr:
                                    strCode = str(oErr)[8:11]
                                    ctBypassInfo = kw.get('ctBypassInfo')
                                    if ctBypassInfo and isinstance(ctBypassInfo, tuple):
                                        strAction, strRequest = ctBypassInfo
                                        strName = oG.oMGroup.strName
                                        bBypassBadAG = oPreProc.oAGProc.fBypassBadData( (strName, strSOR, strAction, strCode) )
                                    else:
                                        bBypassBadAG = False
                                    if bBypassBadAG:
#                                        self.oProf.fStartProfile('LOGS')
                                        strTmp = ''.join(traceback.format_exception(sys.exc_info()[0], sys.exc_info()[1], sys.exc_info()[2]))
                                        strTrace = strTmp.strip()
                                        strTime = Logger.fGetLogTime()
                                        strMsg = "[%s] [error] %s %s %s\nTRACE:\n%s\nREQUEST:\n%s\n\n" % \
                                                 (strTime, strSOR, strAction, str(oErr),
                                                  Logger.fPadLeft(strTrace), Logger.fPadLeft(strRequest))
                                        oPreProc.oLog.fDebug(strMsg)
#                                        self.oProf.fStopProfile('LOGS')
                                    else:
                                        raise oErr
                            else:
                                oP.fAddEmptyDepMultiVal(oG)
                        
                continue

        return oP
        
    #------------------------------------------------------------------------
    #
    #  Get data for DataElement (aka AttributeGroup)
    #
    #  Given a group node, build a group object
    #
    #  Notes:
    #  ====================================
    #  - Check for types, dependencies
    #
    #------------------------------------------------------------------------
    def fXMLGetDE(self, oSubNode, oObj, oMGroup, strSOR, strWriteTrans):
        self.oLog.fDebug('Inside fXMLGetDE', 5)
        #
        # get attribute metadata for group in question
        #
        ctAttrs = oMGroup.fGetAttrNames()

        #
        # setup group object using group metadata that was passed as
        # arg
        #
        oG = TAttrGroup(oMGroup)

        #
        # load dependencies for this group
        #
        self.fLoadGroupDepends(oG)

        #
        # get our list of dependencies that we just loaded (if any)
        #
        ctDeps = ()
        ctDeps = tuple(oG.oDepends.fGetValidKeys())

        #
        # Process those nodes that are considered attributes
        # (e.g. node "Type" is not an attribute)
        #
        ctToProcessNodeNames = ctAttrs
        
        if oMGroup.strName == 'IDs':
            #
            # e.g. in addition to ids like SSN/SISPID/EmployeeID,etc
            # which are attributes mastered by SORs, also add those
            # which are mastered by PR: USCID,etc
            #
            ctToProcessNodeNames += tuple(oObj.oMClass.ctValidPKs)
            
        ctValidNodeNames = ctToProcessNodeNames + ('#text',)
            
        #
        #
        # populate group object with attributes
        #
        for oAttrNode in oSubNode.childNodes:

            #
            # check for exceptions:
            #    * group type
            #    * group dependencies
            #
            if oAttrNode.nodeName == 'Type':
                strText = self.fXMLGetText(oAttrNode)
                oG.strType = strText
                continue
            if len(ctDeps) > 0:
                # group has dependencies...
                strKey = oAttrNode.nodeName
                # check if one of the valid dep keys..
                if strKey in ctDeps:
                    strValue = self.fXMLGetText(oAttrNode)
                    oG.oDepends.fSetGivenItem(strKey, strValue)
                    continue

            #
            # we've handled the exceptions (i.e. non-attributes data)
            # now onto the real attributes...
            #

            if oAttrNode.nodeName not in ctValidNodeNames:
                raise ERepository(111, "Invalid XML, an unrecognized attribute was provided: %s" % (oAttrNode.nodeName))

            if oAttrNode.nodeName not in ctToProcessNodeNames:
                #
                # not data we're interested in..
                #
                continue
            
            #
            # if found one, get the text (data) of that attribute
            #
            strText = self.fXMLGetText(oAttrNode)
            strAttrName = str(oAttrNode.nodeName)
            if (oMGroup.strName == 'IDs') and (strAttrName in oObj.oMClass.ctValidPKs):
                #
                # handle PR-mastered ids differently..
                #
                oObj.fAddPK(strAttrName, strText, self.oEncrypt)
                
            else:
                if strWriteTrans is not None:
                    eval('self.' + strWriteTrans)(oG, oMGroup, strAttrName, strText, strSOR)
                else:
                    #
                    # get attribute object using attribute metadata using
                    # the group metadata we're currently dealing with
                    #
                    oAttr = TAttr(oMGroup.ctMAttrs[(strAttrName,)])
                    oAttr.strValue = strText
                    oAttr.strSOR = strSOR
                    oAttr.fEncrypt()
                    oG.fAddAttr(oAttr)

        # add value if not empty:
        if len(oG.ctAttrs) > 0:
            self.oLog.fDebug('Adding Group: %s' % (str(oG)), 5)
            return oG
        elif len(ctDeps) > 0:
            #
            # still return group, so can delete attributes...
            #
            return oG

        # no attributes found
        return None
        
        # oObj.fAddAG(oG)
                
    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fXMLGetText(self, oNode):
        self.oLog.fDebug('Inside fXMLGetText', 5)
        dataText = ""
        for oSubNode in oNode.childNodes:
            if oSubNode.nodeType == oSubNode.TEXT_NODE:
                dataText += oSubNode.data

        try:
            strText = str(dataText)
        except UnicodeEncodeError:
            strText = unidecode.unidecode(dataText)
        retStr = strText.strip()
        return retStr

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fXMLGetSNs(self, oNode, strName, iMinCount=1, iMaxCount=1):
        self.oLog.fDebug('Inside fXMLGetSNs', 5)
        ctSNs = []
        for oSubNode in oNode.childNodes:
            if oSubNode.nodeName != strName:
                continue
            else:
                ctSNs.append(oSubNode)

        if (len(ctSNs) < iMinCount) or (iMaxCount is not None and len(ctSNs) > iMaxCount):
            raise ERepository(105, 'Invalid number of %s sent (%d): can send between %d and %d at a time.' % (strName, len(ctSNs), iMinCount, iMaxCount))
        
        return ctSNs

    #------------------------------------------------------------------------
    # Check for one and only one BusinessTitle of type
    # Primary when BusinessTitles are specified.
    #------------------------------------------------------------------------
    def fInvalidBusinessTitleGroup(self, oSubNode, strGroupName):
        self.oLog.fDebug('Inside fInvalidBusinessTitleGroup', 5)
        bInvalidBusinessTitleGroup = False
        iPrimaryCount = 0
        bBusinessTitlesFound = False
        bInvalidBusinessTitleFound = False
        for oChildNode in oSubNode.childNodes:
            if oChildNode.nodeName != strGroupName:
                continue
            for oAttrNode in oChildNode.childNodes:
                strAttrName = str(oAttrNode.nodeName)
                strText = self.fXMLGetText(oAttrNode)
                if strAttrName == 'Title':
                    if len(strText) > 0:
                        bBusinessTitlesFound = True
                    else:
                        self.oLog.fError('Invalid BuisnessTitle specified - Empty or null string', 3)
                        bInvalidBusinessTitleFound = True
                else:
                    if strAttrName == 'Primary' and strText == 'Y':
                        iPrimaryCount += 1
        if (bBusinessTitlesFound and iPrimaryCount != 1) or bInvalidBusinessTitleFound:
            if bBusinessTitlesFound and iPrimaryCount != 1:
                self.oLog.fError('Invalid number of Primary BusinessTitles specified (%s) when a single Primary value is expected' % (iPrimaryCount), 3)
            bInvalidBusinessTitleGroup = True

        return bInvalidBusinessTitleGroup

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fProcessRolesAttrs(self, oG, oMGroup, strAttrName, strText, strSOR):
        self.oLog.fDebug('Inside fProcessRolesAttrs', 5)
        if (strAttrName != 'EmployeeStatus') and (strAttrName != 'EmploymentStatus'):
            oAttr = TAttr(oMGroup.ctMAttrs[(strAttrName,)])
            oAttr.strValue = strText
            oAttr.strSOR = strSOR
            oAttr.fEncrypt()
            oG.fAddAttr(oAttr)
            if (strAttrName == 'WdEmployeeStatus'):
                oAttr = TAttr(oMGroup.ctMAttrs[('EmployeeStatus',)])
                oAttr.strValue = self.fConvertWorkdayEmployeeStatus(strText)
                oAttr.strSOR = strSOR
                oAttr.fEncrypt()
                oG.fAddAttr(oAttr)
            if (strAttrName == 'WdEmploymentStatus'):
                oAttr = TAttr(oMGroup.ctMAttrs[('EmploymentStatus',)])
                oAttr.strValue = self.fConvertWorkdayEmploymentStatus(strText)
                oAttr.strSOR = strSOR
                oAttr.fEncrypt()
                oG.fAddAttr(oAttr)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fConvertWorkdayEmployeeStatus(self, strWorkdayEmployeeStatus):
        self.oLog.fDebug('Inside fConvertWorkdayEmployeeStatus', 5)
        sqlSelectPPBSStatus = "select ppbs_status from sor_ppbs_eestatusmap where active_flag = 'Y' and wd_status = '%s'" % (strWorkdayEmployeeStatus)
        retStr = ""

        if (strWorkdayEmployeeStatus is not None) and (len(strWorkdayEmployeeStatus) > 0):
            strPPBSStatus = self.oDB.fSelect(sqlSelectPPBSStatus)
            if strPPBSStatus is not None and len(strPPBSStatus) > 0:
                if len(strPPBSStatus[0]) > 0:
                    if (strPPBSStatus[0][0] is not None):
                        if len(strPPBSStatus[0][0]) > 0:
                            retStr = strPPBSStatus[0][0]
                        else:
                            raise ERepository(103, "Invalid %s: %s" % ("WdEmployeeStatus", strWorkdayEmployeeStatus))
                else:
                    raise ERepository(103, "Invalid %s: %s" % ("WdEmployeeStatus", strWorkdayEmployeeStatus))
            else:
                raise ERepository(103, "Invalid %s: %s" % ("WdEmployeeStatus", strWorkdayEmployeeStatus))

        return str(retStr)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fConvertWorkdayEmploymentStatus(self, strWorkdayEmploymentStatus):
        self.oLog.fDebug('Inside fConvertWorkdayEmploymentStatus', 5)
        sqlSelectPPBSStatus = "select ppbs_status from sor_ppbs_emstatusmap where active_flag = 'Y' and wd_status = '%s'" % (strWorkdayEmploymentStatus)
        retStr = ""

        if (strWorkdayEmploymentStatus is not None) and (len(strWorkdayEmploymentStatus) > 0):
            strPPBSStatus = self.oDB.fSelect(sqlSelectPPBSStatus)
            if len(strPPBSStatus) > 0 and len(strPPBSStatus[0][0]) > 0:
                retStr = strPPBSStatus[0][0]
            else:
                raise ERepository(103, "Invalid %s: %s" % ("WdEmploymentStatus", strWorkdayEmploymentStatus))

        return str(retStr)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fProcessEmployeeInfoAttrs(self, oG, oMGroup, strAttrName, strText, strSOR):
        self.oLog.fDebug('Inside fProcessEmployeeInfoAttrs', 5)
        if (strAttrName != 'WorkPhone') and (strAttrName != 'WorkCell'):
            oAttr = TAttr(oMGroup.ctMAttrs[(strAttrName,)])
            oAttr.strValue = strText
            oAttr.strSOR = strSOR
            oAttr.fEncrypt()
            oG.fAddAttr(oAttr)
            if (strAttrName == 'WdWorkPhone'):
                oAttr = TAttr(oMGroup.ctMAttrs[('WorkPhone',)])
                oAttr.strValue = self.fConvertWorkdayPhoneNumbers(strText)
                oAttr.strSOR = strSOR
                oAttr.fEncrypt()
                oG.fAddAttr(oAttr)
            if (strAttrName == 'WdWorkCell'):
                oAttr = TAttr(oMGroup.ctMAttrs[('WorkCell',)])
                oAttr.strValue = self.fConvertWorkdayPhoneNumbers(strText)
                oAttr.strSOR = strSOR
                oAttr.fEncrypt()
                oG.fAddAttr(oAttr)
            if (strAttrName == 'WdWorkFax'):
                oAttr = TAttr(oMGroup.ctMAttrs[('WorkFax',)])
                oAttr.strValue = self.fConvertWorkdayPhoneNumbers(strText)
                oAttr.strSOR = strSOR
                oAttr.fEncrypt()
                oG.fAddAttr(oAttr)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fConvertWorkdayPhoneNumbers(self, strPhoneNumber):
        self.oLog.fDebug('Inside fConvertWorkdayPhoneNumbers', 5)
        iLen = len(strPhoneNumber)
        if (iLen == 0):
            strPhoneNumber = ""
        elif (iLen < 10):
            self.oLog.fError('Invalid Workday phone number specified %s' % (strPhoneNumber), 3, 0)
            strPhoneNumber = ""
        else:
            tmp = ""
            iCnt = 0
            for ch in strPhoneNumber:
                if (ch >= '0' and ch <= '9'):
                    if (iCnt < 11):
                        tmp += ch
                        iCnt += 1
            if (iCnt >= 10):
                strPhoneNumber = tmp
                indx = strPhoneNumber.find('+', 0, 1);
                if (indx < 0):
                    indx = strPhoneNumber.find('1', 0, 1)
                    if (indx < 0):
                        strPhoneNumber = "+1" + strPhoneNumber
                    else:
                        strPhoneNumber = "+" + strPhoneNumber
                tmp = ""
                iCnt = 0
                for ch in strPhoneNumber:
                    if (ch >= '0' and ch <= '9'):
                        iCnt += 1 
                    if (iCnt == 1 or iCnt == 4 or iCnt == 7):
                        tmp += ch + " "
                    else:
                        if (iCnt < 12):
                            tmp += ch
                strPhoneNumber = tmp
            else:
                self.oLog.fError('Invalid Workday phone number specified %s' % (strPhoneNumber), 3, 0)
                strPhoneNumber = ""
        return str(strPhoneNumber)


    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  No need for locking: since only reading, (plus we're
    #  single-theraded)
    #
    #------------------------------------------------------------------------
    def fQueryXMLExplicit(self, oP, strSOR, ctArgs):
        self.oLog.fDebug('Inside fQueryXMLExplicit: %s: %s' % (strSOR, str(oP)), 5)
        self.fConnect()

        return self.fQueryXML(oP, strSOR, ctArgs)

    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Assume query is for Person object
    #
    #  Note: Since query can have side-effect (currently create can
    #        happen), in cases where database gets updated (as with
    #        create) we must have a way to log such an action with the
    #        USCID affected in the access log.
    #  Update: This is done now for create (when bCreateOnNoMatch=1).
    #
    #------------------------------------------------------------------------
    def fQueryXML(self, oP, strSOR, ctArgs):
        self.oLog.fDebug('Inside fQueryXML: %s: %s' % (strSOR, str(oP)), 5)
        #self.oProf.fStartProfile('fQueryXML')

        bCreateOnNoMatch = ctArgs.get('bCreateOnNoMatch', 0)
        bMatchExact = ctArgs.get('bMatchExact', 0)
        bMatchPartial = ctArgs.get('bMatchPartial', 0)
        
        strXMLFinal = '<NumMatches>%d</NumMatches>\n'

        ctMatches = self.fGetMatchesMT(oP, strSOR,
                                       bException=1,
                                       strReqType='Query',
                                       bMatchExact=bMatchExact,
                                       bMatchPartial=bMatchPartial)

        try:
            # Include number of matches in the response
            iNumMatches = len(ctMatches)
            strXMLFinal %= iNumMatches

            if iNumMatches == 0:
                if bCreateOnNoMatch == 1:
                    # branch off: create record & return
                    return self.fCreateVIPRecord(oP, strSOR, strXMLFinal)

            # By now we have RID of the active record(s)
            for iRID in ctMatches:

                # Get attributes for query results..
                oP = self.fQueryRecord(iRID, oP.oMClass, strSOR)
                
                # Convert to XML..
                strXML = self.fObject2XML(oP, strSOR)

                strXMLFinal += strXML

            self.oDB.fCommit()
            self.fReleaseMatchesMT(ctMatches)
            #self.oProf.fStopProfile('fQueryXML')

            return (strXMLFinal, None)
        
        except ERepository as oErr:
            self.fReleaseMatchesMT(ctMatches)
            self.oDB.fRollback()            
            #self.oProf.fStopProfile('fQueryXML')
            raise oErr

    #------------------------------------------------------------------------
    # 
    #------------------------------------------------------------------------
    def fReadXMLExplicit(self, oP, strSOR):
        self.oLog.fDebug('Inside %s.fReadXMLExplicit: %s: %s' % (str(self.__class__.__name__), strSOR, str(oP)), 5)
        self.fSetup()
        self.fConnect()

        #self.oDB.oCursor.arraysize = 50

        return self.fReadXML(oP, strSOR)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fReadXML(self, oP, strSOR):
        self.oLog.fDebug('Inside TORInterface.fReadXML\n\tSOR: %s\n\tPerson: %s' % (strSOR, str(oP)), 5)
        #self.oProf.fStartProfile('fReadXML')

        #
        # Matching logic in general
        #   1) Match on primary keys (uscid/guid) which
        #      should return just one record at most.
        #   2) Subsequent match on GR attributes - should
        #      result in max 2 matching records.
        #
        # Matching logic for Reads:
        #   Since read by uscid, only one match expected
        #
        
        ctMatches = self.fGetMatchesMT(oP, strSOR)

        try:
            if len(ctMatches) != 1:
                raise ERepository(122, 'Request for Read did not result in a single match; number of matches: %d' % (len(ctMatches)))

            iRID = ctMatches[0]

            # get entire record..
            oP = self.fReadRecord(iRID, oP.oMClass)

            # convert to XML..
            strXML = self.fObject2XML(oP, strSOR)

            self.oDB.fCommit()
            self.fReleaseMatchesMT(ctMatches)
            #self.oProf.fStopProfile('fReadXML')
            
            return strXML
        
        except ERepository as oErr:
            self.fReleaseMatchesMT(ctMatches)
            self.oDB.fRollback()            
            #self.oProf.fStopProfile('fReadXML')
            raise oErr

    #------------------------------------------------------------------------
    #
    #  Given an TObject, converts it to XML
    #
    #  Todo:
    #  - Get term-based info as follows:
    #      attributes for current term
    #      attributes for previous term
    #      attributes for next term
    #  - Tocheck: If not found??
    #
    #
    #  - In theory we can have dependencies besides term, so
    #    we should account for those.
    #  - Currently, we only deal with term dependencies
    #  - Terms need special treatment as follows:
    #    . Depends besides term should be added to Attribute 
    #      Group as XML attributes
    #    . For term, figure out current/next/previous term attribute
    #      groups then package using one of the following options:
    #      o enclose those groups within XML element
    #        indicating the term, e.g.
    #          <ReadResults>
    #            <Person>
    #              <CurrentTermInfo>
    #                <Multi-StudentMajor otherDep1="blah1" otherDep2="blah2">
    #                  <StudentMajor>
    #                    <Post>701</Post>
    #                  </StudentMajor>
    #                  <StudentMajor>
    #                    <Post>702</Post>
    #                  </StudentMajor>
    #                </Multi-StudentMajor>
    #                <StudentTermInfo>
    #                  <StudentYear>U1</StudentYear>
    #                </StudentTermInfo>
    #              </CurrentTermInfo>
    #              <NextTermInfo>
    #                <Multi-StudentMajor otherDep1="blah3" otherDep2="blah4">
    #                  <StudentMajor>
    #                    <Post>703</Post>
    #                  </StudentMajor>
    #                </Multi-StudentMajor>
    #              </NextTermInfo>
    #            </Person>
    #          </ReadResults>
    #      o use values "current"/"next"/"previous" instead of termcode
    #        as XML attributes:
    #          <ReadResults>
    #            <Person>
    #              <Multi-StudentMajor term="current" otherDep1="blah1" otherDep2="blah2">
    #                <StudentMajor>
    #                  <Post>701</Post>
    #                </StudentMajor>
    #                <StudentMajor>
    #                  <Post>702</Post>
    #                </StudentMajor>
    #              </Multi-StudentMajor>
    #              <StudentTermInfo>
    #                <StudentYear>U1</StudentYear>
    #              </StudentTermInfo>
    #              <Multi-StudentMajor term="next" otherDep1="blah3" otherDep2="blah4">
    #                <StudentMajor>
    #                  <Post>703</Post>
    #                </StudentMajor>
    #              </Multi-StudentMajor>
    #            </Person>
    #          </ReadResults>
    #
    #------------------------------------------------------------------------
    def fObject2XML(self, oP, strSOR):
        self.oLog.fDebug('Inside TORInterface.fObject2XML', 5)

        iSORID = self.ctSOR2ID[strSOR]
        oReadTrans = Hooks.TReadTrans()

        strXML = ''

        # generate historical ids xml:
        for ctPKs in oP.ctHistoricalPKs:
            strXML += '  <HistoricalIDs>\n'
            for strKey in oP.oMClass.ctValidPKs:
                if strKey in ctPKs:
                    strXML += '    <%s>%s</%s>\n' % (strKey, ctPKs[strKey], strKey)
            strXML += '  </HistoricalIDs>\n'

        strXML = '  <Multi-HistoricalIDs>\n%s  </Multi-HistoricalIDs>\n' % (strXML)

        bFoundIDs = 0
        bFoundEmpInfo = False
        ctGroups = list(oP.ctAttrGroups.items())
        ctGroups.sort()
        for (strGroupKey, ctGroup) in ctGroups:
            strXMLMGroup = ''
            if len(ctGroup) == 0:
                continue
            # since can be multi-valued..
            for oGroup in ctGroup:
                strXMLGroup = ''
                strType = oGroup.strType
                iType = None
                if strType:
                    iType = oGroup.oMGroup.fType2TypeID(strType)

                if oGroup.oMGroup.strName == 'IDs':
                    bFoundIDs = 1
                    for strKey in oP.oMClass.ctValidPKs:
                        if strKey in oP.ctPKs:
                            strXMLGroup += '    <%s>%s</%s>\n' % (strKey, oP.ctPKs[strKey], strKey)

                if oGroup.oMGroup.strName == 'EmployeeInfo' and bFoundEmpInfo == False:
                    bFoundEmpInfo = True
                    oReadTrans.GetDeptInfo(self.oDB, oGroup.ctAttrs)

                ctAttrs = list(oGroup.ctAttrs.items())
                ctAttrs.sort()
                for (strAttrKey, oAttr) in ctAttrs:
                    iAuthLevel, strReadTrans = oAttr.oMAttr.fGetAuthLevel(iSORID, iType)
                    if (iAuthLevel is None):
                        continue
                    if (iAuthLevel < 0 and strSOR != 'ADMIN'):
                        continue
                    
                    if strReadTrans is not None:
                        # reflect into the hook
                        # we expect this to fail badly if the hook does not exist
                        # or does not match the metadata-specified function
                        strXMLGroup += eval('oReadTrans.' + strReadTrans)(self.oDB, oGroup.oDepends, oAttr)
                    else:
                        strAttrName = oAttr.oMAttr.strName
                        strVal = saxutils.escape(oAttr.strValue)
                        strXMLGroup += '    <%s>%s</%s>\n' % (strAttrName, strVal, strAttrName)

                if strXMLGroup > '':
                    #
                    # Attach the following for each attribute group:
                    #   - type if any
                    #   - dependencies if any
                    #   - group name
                    #
                    if strType is not None:
                        strXMLGroup = '    <Type>%s</Type>\n' % (strType) + strXMLGroup
                    if oGroup.oMGroup.fHasDepends() and oGroup.oMGroup.strAllowMult == 'N':
                        #
                        # If has dependencies, include deps as XML attributes
                        # However, for multi-valued attributes, deps should be
                        # be included in element starting with Multi-* (see below)
                        #
                        (bSkipGroup,strXMLGroup) = self._fAttrGroupDependencies2XML(strXMLGroup, oGroup, strSOR)
                        if bSkipGroup:
                            continue
                    else:
                        strGroupName = oGroup.oMGroup.strName
                        strXMLGroup = '  <%s>\n%s  </%s>\n' % (strGroupName, strXMLGroup, strGroupName)
                    strXMLMGroup += strXMLGroup

            if strXMLMGroup > '':
                if ctGroup[0].oMGroup.strAllowMult == 'Y':
                    if oGroup.oMGroup.fHasDepends():
                        (bSkipGroup,strXMLMGroup) = self._fAttrGroupDependencies2XML(strXMLMGroup, ctGroup[0], strSOR)
                        if bSkipGroup:
                            continue
                    else:
                        strGroupName = ctGroup[0].oMGroup.strName
                        strXMLMGroup = '  <Multi-%s>\n%s  </Multi-%s>\n' % (strGroupName, strXMLMGroup, strGroupName)

                strXML += strXMLMGroup

        if bFoundIDs == 0:
            strXMLGroup = ''
            for strKey in oP.oMClass.ctValidPKs:
                if strKey in oP.ctPKs:
                    strXMLGroup += '    <%s>%s</%s>\n' % (strKey, oP.ctPKs[strKey], strKey)
            strXML += '  <IDs>\n%s  </IDs>\n' % (strXMLGroup)

        strXML += oReadTrans.AttachMiscGroup()

        strClassName = oP.oMClass.strName
        strXML = '<%s>\n%s</%s>\n' % (strClassName, strXML, strClassName)
        # self.oLog.fDebug('XML: %s' % (strXML), 5)
        return strXML
    
    
    def fGetHistoricalUSCIDXML(self, oPerson):
        self.oLog.fDebug('Inside fGetHistoricalUSCIDXML', 5)
        # generate historical ids xml:
        strXML = ''
        
        for ctPKs in oPerson.ctHistoricalPKs:
            strXML += '  <HistoricalIDs>\n'
            for strKey in oPerson.oMClass.ctValidPKs:
                if strKey in ctPKs:
                    strXML += '    <%s>%s</%s>\n' % (strKey, ctPKs[strKey], strKey)
            strXML += '  </HistoricalIDs>\n'

        return '  <Multi-HistoricalIDs>\n%s  </Multi-HistoricalIDs>\n' % (strXML)

                
    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:ROLES >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Package attribute group dependencies as XML
    #
    #  If SOR is GDS and dependency is TermCode then:
    #  - only include attribute group if TermCode maps to one of:
    #    ["current","next","previous"]
    #  - instead of including TermCode as XML attribute, include Term
    #    as XML attribute with value one of ["current","next","previous"]
    #
    #------------------------------------------------------------------------
    def _fAttrGroupDependencies2XML(self, strXML, oGroup, strSOR):
        self.oLog.fDebug('Inside fAttrGroupDependencies2XML', 5)
        strGroupName = oGroup.oMGroup.strName
        strXMLDepAttrib = ''
        strXMLDepElement = ''

        bSkipGroup = 0
        
        #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:ROLES >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:ENROL >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        if strGroupName == 'CourseRole':
            for strDepKey, strDepVal in oGroup.oDepends.fGetGivenItems():
                if strDepKey == 'TermCode' and (strSOR == 'GDS' or strSOR == 'ADMIN'):
                    strTerms = self.oSISUtil.fGetCurrentTerm(self.oDB,
                                                             bWithAdjTerms=1)
                    strCurr, strNext, strPrev = strTerms
                    if strDepVal == strCurr:
                        strXMLDepAttrib += ' Term="Current"'
                    elif strDepVal == strNext:
                        strXMLDepAttrib += ' Term="Next"'
                    elif strDepVal == strPrev:
                        strXMLDepAttrib += ' Term="Previous"'
                    else:
                        bSkipGroup = 1
                        break
                strXMLDepElement += '    <%s>%s</%s>\n' % (strDepKey,strDepVal,strDepKey)
            if bSkipGroup:
                return (1, '')
            strTemplate = '  <%s %s>\n%s%s  </%s>\n'
            strXML = strTemplate % (strGroupName, strXMLDepAttrib, strXMLDepElement, strXML, strGroupName)
            return (0, strXML)

        for strDepKey, strDepVal in oGroup.oDepends.fGetGivenItems():
            if strDepKey == 'TermCode' and (strSOR == 'GDS' or strSOR == 'ADMIN'):
                strTerms = self.oSISUtil.fGetCurrentTerm(self.oDB,
                                                         bWithAdjTerms=1)
                strCurr, strNext, strPrev = strTerms
                if strDepVal == strCurr:
                    strXMLDepAttrib += ' Term="Current"'
                elif strDepVal == strNext:
                    strXMLDepAttrib += ' Term="Next"'
                elif strDepVal == strPrev:
                    strXMLDepAttrib += ' Term="Previous"'
                else:
                    bSkipGroup = 1
                    break
            else:
                strXMLDepAttrib += ' %s="%s"' % (strDepKey,strDepVal)

        if bSkipGroup:
            return (1, '')
        
        if oGroup.oMGroup.strAllowMult == 'Y':
            strTemplate = '  <Multi-%s %s>\n%s  </Multi-%s>\n'
        else:
            strTemplate = '  <%s %s>\n%s  </%s>\n'

        strXMLDepAttrib = strXMLDepAttrib.replace('  ',' ')
        strXML = strTemplate % (strGroupName, strXMLDepAttrib, strXML, strGroupName)
        #strXML = strXML.replace('  ',' ')

        return (0, strXML)


#****************************************************************************
#
#  Interface for repository for PERSON objects only
#
#****************************************************************************

class TGPRInterface(TORInterface):

    #
    # sql
    #

    # used for fSetAsActiveUSCID:
    sqlSelectUSCIDInfo = """
       select RID, Active_Flag from Person
       where USCID = ?
       """

    sqlSelectMergeInfo = """
       select ID, Merged_Into_RID, Final_RID
       from Person_Merge
       where Merged_RID = ?
       """

    sqlDeleteMergeLink = """
       delete from Person_Merge
       where ID = ?
       """

    sqlReactivateRecord = """
       update Person
       set Active_Flag = 'Y',
           Note = ?,
           Modified_DTM = sysdate
       where RID = ?
       """

    sqlMergeRID = """
      select merged_rid
      from person_merge
      where final_rid = ?
      """


    sqlInsertUserDelta = """
      insert into user_delta
      (user_id, action)
      values
      ((select SUBSTR(p.uscid, 3) from person p where p.rid = ?), ?)
      """

    sqlIsStudent = """
      select 1
      from person p inner join person_roles pr on p.rid = pr.rid
      where p.active_flag = 'Y'
        and NVL(p.test_flag, 'N') != 'Y'
        and (pr.studentstatus_value = 'Active' or
             pr.studentstatus_value = 'Inactive')
        and pr.rid = ?
      """

    sqlIsStudentNoActiveFlagCheck = """
      select 1
      from person p inner join person_roles pr on p.rid = pr.rid
      where NVL(p.test_flag, 'N') != 'Y'
        and (pr.studentstatus_value = 'Active' or
             pr.studentstatus_value = 'Inactive')
        and pr.rid = ?
      """

    sqlHasStudentCertifiedTransferedOrReturned = """
      select 1
      from person p inner join person_studentterminfo ps on p.rid = ps.rid
      where p.active_flag = 'Y'
        and NVL(p.test_flag, 'N') != 'Y'
        and ((ps.certificationdate_value is not null and
              ps.certificationdate_value <> '0-' and
              ps.certificationdate_dtm >= trunc(sysdate)) or
             (ps.returndate_value is not null and
              ps.returndate_value <> '0-' and
              ps.returndate_dtm >= trunc(sysdate)) or
             (NVL(ps.transfer_value, 'N') = 'Y') and
              ps.transfer_dtm >= trunc(sysdate))
        and ps.rid = ?
      """

    sqlIsStudentDeceasedOrExpelled = """
      select 1
      from person p inner join person_studentpost ps on p.rid = ps.rid
      where p.active_flag = 'Y'
        and NVL(p.test_flag, 'N') != 'Y'
        and (ps.postexpreason_value = 'X' or ps.postexpreason_value = 'XX')
        and (ps.postexpreason_dtm >= trunc(sysdate))
        and ps.rid = ?
      """

    sqlCheckPersonRolesStatus = """
      select 1
      from person_roles pr
      where pr.rid = ?
      """

    sqlUpdateStudentStatusActive = """
      update person_roles pr
      set pr.modified_DTM = sysdate, pr.studentstatus_value = 'Active', pr.studentstatus_SOR = (select sor_id from meta_sor where sor_name = 'SIS'), pr.studentstatus_DTM = sysdate
      where pr.rid = ?
      """

    sqlUpdateStudentStatusInactive = """
      update person_roles pr
      set pr.modified_DTM = sysdate, pr.studentstatus_value = 'Inactive', pr.studentstatus_SOR = (select sor_id from meta_sor where sor_name = 'SIS'), pr.studentstatus_DTM = sysdate
      where pr.rid = ?
      """

    sqlInsertStudentStatusActive = """
      insert into person_roles pr
      (pr.id, pr.rid, pr.create_DTM, pr.modified_DTM, pr.studentstatus_value, pr.studentstatus_SOR, pr.studentstatus_DTM)
      values
      (SEQ_IDS.nextval, ?, sysdate, sysdate, 'Active', (select sor_id from meta_sor where sor_name = 'SIS'), sysdate)
      """

    sqlInsertStudentStatusInactive = """
      insert into person_roles pr
      (pr.id, pr.rid, pr.create_DTM, pr.modified_DTM, pr.studentstatus_value, pr.studentstatus_SOR, pr.studentstatus_DTM)
      values
      (SEQ_IDS.nextval, ?, sysdate, sysdate, 'Inactive', (select sor_id from meta_sor where sor_name = 'SIS'), sysdate)
      """

    sqlIsEmployee = """
      select 1
      from person p inner join Person_Roles pr on p.rid = pr.rid inner join Person_Demo pd on p.rid = pd.rid
      where p.active_flag = 'Y'
        and p.rid = ?
        and (pr.employeestatus_value = '0-Faculty' or
             pr.employeestatus_value = '0-Staff')
        and (pr.employmentstatus_value = '0-Active' or
             pr.employmentstatus_value = '0-Inactive')
        and pr.wdemployeestatus_value is not null
        and pr.wdemployeestatus_value != '0-'
        and pd.birthdate_value is not null
        and pd.birthdate_value != '0-'
      """

    sqlIsEmployeeNoActiveFlagCheck = """
      select 1
      from person p inner join Person_Roles pr on p.rid = pr.rid inner join Person_Demo pd on p.rid = pd.rid
      where p.rid = ?
        and (pr.employeestatus_value = '0-Faculty' or
             pr.employeestatus_value = '0-Staff')
        and (pr.employmentstatus_value = '0-Active' or
             pr.employmentstatus_value = '0-Inactive')
        and pr.wdemployeestatus_value is not null
        and pr.wdemployeestatus_value != '0-'
        and pd.birthdate_value is not null
        and pd.birthdate_value != '0-'
      """

    sqlIsGuest = """
      select 1
      from person p inner join person_ids pi on p.rid = pi.rid
      where p.active_flag = 'Y'
        and pi.rid = ?
        and pi.ivipid_value is not null
      """

    sqlIsGuestNoActiveFlagCheck = """
      select 1
      from person_ids pi
      where pi.rid = ?
        and pi.ivipid_value is not null
      """

    sqlNotInKeepActive = """
      select 1
      from dual
      where not exists (select ka.rid
                        from person p inner join keep_active ka on p.rid = ka.rid
                        where p.active_flag = 'Y'
                          and ka.rid = ?)
      """

#   sqlKeepActive = """
#     select 1
#     from person p inner join keep_active ka on p.rid = ka.rid
#     where p.active_flag = 'Y'
#     and ka.rid = ?
#     """

#   sqlKeepActiveNoActiveFlagCheck = """
#     select 1
#     from keep_active ka
#     where ka.rid = ?
#     """


    # fGetMatches:
    sqlSelectMatchesGR = """
       select p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in ('Reported', 'Verified'))
       """

    # fGetMatches:
    sqlSelectMatchesSR = """
       select p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and (pn.GTYPE_ID = 1 or pn.GTYPE_ID = 2)
       """

    # fGetMatches:
    sqlSelectMatchesSRnotUSCID = """
       select p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and (pn.GTYPE_ID = 1 or pn.GTYPE_ID = 2)
       and p.USCID != ?
       """

    # fMergeRecords:
    sqlCountDoNotMerge = """
       select count(*) from PERSON_DO_NOT_MERGE
       where (RID1 = ? and RID2 = ?)
          or (RID1 = ? and RID2 = ?)
       """

    sqlCountTestRecord = """
       select count(*) from PERSON
       where (RID = ? or RID = ?)
         and (TEST_FLAG = 'Y')
       """

    sqlInsertDoNotMerge = """
       insert into PERSON_DO_NOT_MERGE
       (ID, CREATE_DTM, MODIFIED_DTM, RID1, RID2, NOTE) values (SEQ_IDS.nextval, sysdate, sysdate, ?, ?, ?)
       """
    
    sqlUpdateAsMerged = """
       update PERSON
       set MODIFIED_DTM = sysdate,
           ACTIVE_FLAG  = 'N',
           NOTE = ?
       where RID = ?
       """
    
    sqlUpdateOldMerges = """
       update PERSON_MERGE
       set FINAL_RID = ?,
           MODIFIED_DTM = sysdate,
           NOTE = ?
       where FINAL_RID = ?
       """

    sqlUpdateOldDoNotMergesTemplate = """
       update PERSON_DO_NOT_MERGE
       set MODIFIED_DTM = sysdate,
           RID%(RIDNUM)d = ?
       where RID%(RIDNUM)d = ?
       """

    sqlInsertNewMerge = """
       insert into PERSON_MERGE
       (ID, MERGED_RID, MERGED_INTO_RID, FINAL_RID, NOTE, CREATE_DTM, MODIFIED_DTM)
       values (SEQ_IDS.nextval, ?, ?, ?, ?, sysdate, sysdate)
       """

    # fUnmergeRecords
    sqlDeleteMerge = """
       delete from %s_Merge
       where Final_RID = ?
       and   Merged_RID = ?
       """
    
    sqlSelectSORCount = """
       select count(RID) from PERSON_IDS
       where RID = ?
       and %s is not null
       and %s != '0-'
       """

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def __init__(self, oLog = Logger.TLogger('TGPRInterface',
                                             iPrintLevel=oInit.golden.iPrintLevel,
                                             strToEmail=oInit.golden.strErrorNotifyFull)):
        TORInterface.__init__(self, oLog)

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fCheckForNewStudentStatus(self, iRID, oP):
        self.oLog.fDebug('Inside fCheckForNewStudentStatus', 5)
        if (self.oDB.fSelect(self.sqlHasStudentCertifiedTransferedOrReturned, [iRID])):
            return True
        else:
            return False

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fCheckForExpelledOrDeceasedStatus(self, iRID, oP):
        self.oLog.fDebug('Inside fCheckForExpelledOrDeceasedStatus', 5)
        if (self.oDB.fSelect(self.sqlIsStudentDeceasedOrExpelled, [iRID])):
            return True
        else:
            return False

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fCheckForPersonRolesRecord(self, iRID):
        self.oLog.fDebug('Inside fCheckForPersonRolesRecord', 5)
        if (self.oDB.fSelect(self.sqlCheckPersonRolesStatus, [iRID])):
            return True
        else:
            return False

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fUpdateStudentStatusActive(self, iRID):
        self.oLog.fDebug('Inside fUpdateStudentStatusActive', 5)
        try:
            if (self.oDB.fSelect(self.sqlNotInKeepActive, [iRID])):
                self.oDB.fExec(self.sqlUpdateStudentStatusActive, [iRID])
                self.oDB.fCommit()
            else:
                self.oLog.fDebug('RID: ' + str(iRID) + ' exists in the keep_active table', 3)
            return
        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fUpdateStudentStatusInactive(self, iRID):
        self.oLog.fDebug('Inside fUpdateStudentStatusInactive', 5)
        try:
            if (self.oDB.fSelect(self.sqlNotInKeepActive, [iRID])):
                self.oDB.fExec(self.sqlUpdateStudentStatusInactive, [iRID])
                self.oDB.fCommit()
            else:
                self.oLog.fDebug('RID: ' + str(iRID) + ' exists in the keep_active table', 3)
            return
        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fInsertStudentStatusActive(self, iRID):
        self.oLog.fDebug('Inside fInsertStudentStatusActive', 5)
        try:
            if (self.oDB.fSelect(self.sqlNotInKeepActive, [iRID])):
                self.oDB.fExec(self.sqlInsertStudentStatusActive, [iRID])
                self.oDB.fCommit()
            else:
                self.oLog.fDebug('RID: ' + str(iRID) + ' exists in the keep_active table', 3)
            return
        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fInsertStudentStatusInactive(self, iRID):
        self.oLog.fDebug('Inside fInsertStudentStatusInactive', 5)
        try:
            if (self.oDB.fSelect(self.sqlNotInKeepActive, [iRID])):
                self.oDB.fExec(self.sqlInsertStudentStatusInactive, [iRID])
                self.oDB.fCommit()
            else:
                self.oLog.fDebug('RID: ' + str(iRID) + ' exists in the keep_active table', 3)
            return
        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

    #------------------------------------------------------------------------
    #
    #  Makes sure given USCID is the active one
    #
    #------------------------------------------------------------------------
    def fSetAsActiveUSCIDExplicit(self, strUSCIDGiven, strSOR):
        self.fSetup()
        try:
            self.oLog.fDebug('fSetAsActiveUSCIDExplicit: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()
            self.oLog.fDebug('fSetAsActiveUSCIDExplicit: oLockAdd Acquired', 5)
 
            return self.fSetAsActiveUSCID(strUSCIDGiven, strSOR)

        finally:
            self.oLog.fDebug('fSetAsActiveUSCIDExplicit: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fSetAsActiveUSCIDExplicit: oLockAdd Released', 5)

    #------------------------------------------------------------------------
    #
    #  This method ...
    #
    #------------------------------------------------------------------------
    def fCheckMyAccess(self, iRID, bCheckActive, strAction):
        if bCheckActive:
            ctRes = self.oDB.fSelect(self.sqlIsStudent, [iRID])
        else:
            ctRes = self.oDB.fSelect(self.sqlIsStudentNoActiveFlagCheck, [iRID])
        if len(ctRes) > 0:
            try:
                self.oDB.fExec(self.sqlInsertUserDelta, [iRID, strAction])
                self.oDB.fCommit()
                return
            except ERepository as oErr:
                self.oDB.fRollback()
                raise oErr

        if bCheckActive:
            ctRes = self.oDB.fSelect(self.sqlIsEmployee, [iRID])
        else:
            ctRes = self.oDB.fSelect(self.sqlIsEmployeeNoActiveFlagCheck, [iRID])
        if len(ctRes) > 0:
            try:
                self.oDB.fExec(self.sqlInsertUserDelta, [iRID, strAction])
                self.oDB.fCommit()
                return
            except ERepository as oErr:
                self.oDB.fRollback()
                raise oErr

        if bCheckActive:
            ctRes = self.oDB.fSelect(self.sqlIsGuest, [iRID])
        else:
            ctRes = self.oDB.fSelect(self.sqlIsGuestNoActiveFlagCheck, [iRID])
        if len(ctRes) > 0:
            try:
                self.oDB.fExec(self.sqlInsertUserDelta, [iRID, strAction])
                self.oDB.fCommit()
                return
            except ERepository as oErr:
                self.oDB.fRollback()
                raise oErr

#       if bCheckActive:
#           ctRes = self.oDB.fSelect(self.sqlKeepActive, [iRID])
#       else:
#           ctRes = self.oDB.fSelect(self.sqlKeepActiveNoActiveFlagCheck, [iRID])
#       if len(ctRes) > 0:
#           try:
#               self.oDB.fExec(self.sqlInsertUserDelta, [iRID, strAction])
#               self.oDB.fCommit()
#               return
#           except ERepository as oErr:
#               self.oDB.fRollback()
#               raise oErr

    #------------------------------------------------------------------------
    #
    #  Makes sure given USCID is the active one
    #
    #------------------------------------------------------------------------
    def fSetAsActiveUSCID(self, strUSCIDGiven, strSOR):
        self.fSetup()

        # get active information on given USCID
        oMClass = self.ctMClasses[('Person',)]
        oPKeep = TObject(oMClass)
        oPKeep.fAddPK('USCID', strUSCIDGiven, self.oEncrypt)
        ctUSCIDInfo = self.oDB.fSelect(self.sqlSelectUSCIDInfo, [oPKeep.ctEPKs['USCID']])

        if len(ctUSCIDInfo) == 0:
            raise ERepository(115, "SOR provided USCID that does not exist in PR: %s" % (strUSCIDGiven))

        (iRIDGiven, strIsActive) = ctUSCIDInfo[0]

        # check if already active, if so, done.
        if strIsActive == 'Y':
            return oPKeep
            
        # if not, two or three records are involved:
        #   1. the inactive one (the given USCID)
        #   2. the one the inactive is pointing to.
        #   3. the "final" and active USCID  (possibly the same as #2)
        
        # find the one pointing to, and final active one.
        ctMerges = self.oDB.fSelect(self.sqlSelectMergeInfo, [iRIDGiven])

        if len(ctMerges) == 0:
            raise ERepository(119, "SOR Provided a USCID to be set active that was never merged: %s" % (strUSCIDGiven))

        if len(ctMerges) > 1:
            raise ERepository(211, "The given USCID is marked as having been merged into multiple records: %s" % (strUSCIDGiven))
                                  
        (iMergeID, iRIDMergedInto, iRIDFinal) = ctMerges[0]
            
        # remove the link between inactive to where it's pointing to.
        self.oDB.fExec(self.sqlDeleteMergeLink, [iMergeID])
            
        # set given USCID as active
        self.oDB.fExec(self.sqlReactivateRecord, ['SetAsActiveUSCID - Reactivated', iRIDGiven])

        # make a new link from Final to Given
        self.fMergeRecords(iRIDFinal, iRIDGiven, strSOR, strNote = 'SetAsActiveUSCID')
            
        self.oDB.fCommit()
        return oPKeep

    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Given person object & an SOR, update the database accordingly
    #   return: list of objects with attributes modified
    #
    #  Note: Needs to be multi-thread safe
    #
    #   Input:
    #     oP: Person Object
    #     strSOR: SOR which provided this request
    #
    #   Output tuple:
    #     oUP: Person Object containing modified attributes
    #     ctAllErasedP: list of Person Objects containing overwritten attributes
    #     oIDsP: Person Object containing all the IDs attributes of final record
    #
    #  Further Notes:
    #  - oUP & ctAllErasedP are used to decide if a merge happened & to log
    #    in merge logs.
    #  - oIDsP is used to extract the USCID to send back as response.
    #
    #------------------------------------------------------------------------
    def fAddExplicit(self, oP, strSOR):
        self.oLog.fDebug('fAddExplicit: %s: %s' % (strSOR, str(oP)), 5)
        #self.oProf.fStartProfile('fAddExplicit')
        self.fSetup()

        try:
            self.oLog.fDebug('fAddExplicit: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()  # start lock
            self.oLog.fDebug('fAddExplicit: oLockAdd Acquired', 5)
            self.fConnect()
            oUP, ctAllErasedP, oIDsP = self.fAdd(oP, strSOR)
            self.oDB.fCommit()
            return oUP, ctAllErasedP, oIDsP
        
        except Exception as oErr:
            strExceptionName = str(type(oErr).__name__)
            self.oLog.fDebug('fAddExplicit: Exception caught: %s' % (strExceptionName), 5)
            strErr = str(oErr)
            self.oLog.fDebug('fAddExplicit: Exception Details: %s' % (strErr), 5)
            self.oLog.fDebug(''.join(traceback.format_exception(sys.exc_info()[0], sys.exc_info()[1], sys.exc_info()[2])), 5)
            self.oDB.fRollback()
            self.oLog.fError(str(oP), 5)
            raise oErr

        finally:
            self.oLog.fDebug('fAddExplicit: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fAddExplicit: oLockAdd Released', 5)
            #self.oProf.fStopProfile('fAddExplicit')
           
    #------------------------------------------------------------------------
    #
    #  oP:
    #    input record, used to search for matches as well as
    #    update/insert if bAllowUpdates is set to 1
    #  strSOR:
    #    the SOR performing the action
    #  oUP:
    #    the record that is being updated, typically set to None,
    #    unless called from anoter action (such as fMergeExplicit)
    #  bAllowUpdates:
    #    whether or not allows inserts / updates (merges
    #    always allowed).  Useful for fMergeExplicit since it wants to
    #    SEARCH for matches, yet does't wants to update records with
    #    search info.
    #
    #------------------------------------------------------------------------
    def fAdd(self, oP, strSOR, oUP = None, bAllowUpdates=1):
            self.oLog.fDebug('Inside fAdd: SOR = %s' % (strSOR), 5)
        
            if oUP is None:
                oUP = TObject(oP.oMClass)

            #
            # Contains fields that were erased (can be mulitple on merges)
            #
            ctAllErasedP = []

            # iVIP HACK START
            if strSOR == 'iVIP':
                if not self.fCheckAttrPresence(oP, 'IDs', 'iVIPID'):
                    raise ERepository(128, 'Did not provide iVIPID on a Create/Update')
            # iVIP HACK END

            # SIS HACK START
            strUSCID =  oP.ctPKs.get('USCID', None)
            # SIS HACK END

            iLoopCounter = 0
            while 1:
                iLoopCounter += 1
                if iLoopCounter > 50:
                    raise ERepository(210, "Internal looped too many times: fAdd (GPR)")
                
                #self.oProf.fStartProfile('fAdd:GetMatches')

                #
                # Matched RIDs are locked: must release when done.
                #
                # MT changes:
                #   fGetMatchesMT should return a list of RIDs for records
                #   that matched as follows:
                #   - in case of SOR Create:
                #     - Total matches = 0 prior to Filter -> Insert
                #     - Total matches = 1 prior to Filter -> Update
                #     - Total matches > 1 prior to Filter -> Filter
                #     - After Filter, total matches = 0 -> Insert
                #     - After Filter, total matches = 1 -> Update
                #     - After Filter, total matches > 1 -> Merge
                #   - in case of SOR Update:
                #     - Total matches = 0 prior to Filter -> Error
                #     - Total matches = 1 prior to Filter -> Update
                #     - Total matches > 1 prior to Filter -> Filter
                #     - After Filter, total matches = 0 -> Error (disallow)
                #     - After Filter, total matches = 1 -> Update
                #     - After Filter, total matches > 1 -> Merge
                #
                ctOrigMatches = self.fGetMatchesMT(oP, strSOR)

                #
                # List of RIDs we will work with.
                # Matches are by PK & GR info (if provided).
                #
                ctMatches = ctOrigMatches[:]

                try:
                    #self.oProf.fStopProfile('fAdd:GetMatches')

                    ctErasedP = []
                    bHasMerged = False
                    bChanged = False
                
                    #
                    # Create new record
                    #
                    if len(ctMatches) == 0 and bAllowUpdates:
                        if not oCreateFilter.fCreateFilter(oP, strSOR, self.oLog):
                            raise ERepository(131, "SOR did not provide information required for person create")

                        #self.oProf.fStartProfile('fAdd:Insert')

                        # create record shell in db
                        self.fCreateRecordShell(oUP, oP, strSOR)
                        # update record shell in db with SOR data
                        (oErasedP, bChanged) = self.fUpdateRecordAGs(oUP, oP)
                        ctErasedP.append(oErasedP)

                        #self.oProf.fStopProfile('fAdd:Insert')

                        if (bChanged):
                            iRID = oUP.iRID
                            if (self.fCheckForNewStudentStatus(iRID, oP)):
                                if (self.fCheckForPersonRolesRecord(iRID)):
                                    self.fUpdateStudentStatusActive(iRID)
                                else:
                                    self.fInsertStudentStatusActive(iRID)
                            if (self.fCheckForExpelledOrDeceasedStatus(iRID, oP)):
                                if (self.fCheckForPersonRolesRecord(iRID)):
                                    self.fUpdateStudentStatusInactive(iRID)
                                else:
                                    self.fInsertStudentStatusInactive(iRID)
                            self.fCheckMyAccess(oUP.iRID, True, 'Insert')


                    #
                    # Update existing record
                    #
                    if len(ctMatches) == 1 and bAllowUpdates:
                        #self.oProf.fStartProfile('fAdd:Update')

                        oUP.iRID = ctMatches[0]
                        # update record shell
                        (oErasedP, bChanged) = self.fUpdateRecord(oUP, oP, strSOR)
                        ctErasedP.append(oErasedP)

                        #self.oProf.fStopProfile('fAdd:Update')

                        if (bChanged):
                            iRID = oUP.iRID
                           #self.fCheckAttrPresence(oP, 'StudentTermInfo', 'CertificationDate'):
                            if (self.fCheckForNewStudentStatus(iRID, oP)):
                                if (self.fCheckForPersonRolesRecord(iRID)):
                                    self.fUpdateStudentStatusActive(iRID)
                                else:
                                    self.fInsertStudentStatusActive(iRID)
                            if (self.fCheckForExpelledOrDeceasedStatus(iRID, oP)):
                                if (self.fCheckForPersonRolesRecord(iRID)):
                                    self.fUpdateStudentStatusInactive(iRID)
                                else:
                                    self.fInsertStudentStatusInactive(iRID)
                            self.fCheckMyAccess(oUP.iRID, True, 'Update')
                    #
                    # Merge existing records
                    #
                    if len(ctMatches) > 1:
                        #self.oProf.fStartProfile('fAdd:Merge')

                        bHasMerged = True
                    
                        iLoopCounter = 0
                        while len(ctMatches) > 1:
                            iLoopCounter += 1
                            if iLoopCounter > 50:
                                raise ERepository(210, "Internal looped too many times: fAdd (GPR) - merges")

                            #
                            # This while loop takes care of merging records
                            # that already exist in DB
                            #
                            
                            # SIS HACK START
                            # NOTE: This hack is overloaded for Explicit merge:
                            #       wants to keep USCID that was explicity asked for.
                            (oUP.iRID, oErasedP) = self.fSISHackMergeRecords(ctMatches[0],
                                                                             ctMatches[1],
                                                                             strSOR,
                                                                             strUSCID)
                            # SIS HACK END
                            
                            # DE-SIS HACK:
                            #(oUP.iRID, oErasedP) = self.fAutoMergeRecords(ctMatches[0],
                            #                                              ctMatches[1],
                            #                                              strSOR)

                            ctErasedP.append(oErasedP)
                        
                            if int(ctMatches[0]) == int(oUP.iRID):
                                del ctMatches[0]
                            else:
                                del ctMatches[1]

                        #
                        # Now that the while loop has taken care of merging records
                        # already in the DB, we can update the final record with data
                        # provided by the SOR
                        #

                        # update record:
                        (oErasedP, bChanged) = self.fUpdateRecord(oUP, oP, strSOR)
                        ctErasedP.append(oErasedP)

                        #self.oProf.fStopProfile('fAdd:Merge')

                        self.oLog.fDebug('fAdd: Merged existing records - Loop: %s' % (str(iLoopCounter)), 5)
                        self.oLog.fDebug('Primary RID: ' + str(oUP.iRID), 5)
                        self.fCheckMyAccess(oUP.iRID, False, 'Update')
                        ctRID = self.oDB.fSelect(self.sqlMergeRID, [oUP.iRID])
                        if len(ctRID) > 0:
                            for tRID in ctRID:
                                iRID = tRID[0]
                                if iRID in ctOrigMatches:
                                    self.oLog.fDebug('Historical RID: ' + str(iRID), 5)
                                    self.fCheckMyAccess(iRID, False, 'Update')

                    ctAllErasedP.extend(ctErasedP)

                    #
                    # check if GR changed, and hence we need to re-scan for updates, etc:
                    #
                    # Notes:
                    #   . We check if GR info was updated.
                    #   . In case of NO merges:
                    #     - If no change, then we expect no further matches
                    #       (scenarios: Create, Update)
                    #     - If all attributes changed, still expect no
                    #       further matches (since we're rescanning
                    #       for GR matches but those have already been
                    #       taken care of)
                    #       (scenarios: Create, Update, Merge)
                    #     - If some but not all GR attributes change, we can
                    #       expect further matches, so get set of matches.
                    #       (scenarios: Create, Update)
                    #
                    if (not self.fCheckChangedGR(ctErasedP)) and (not bHasMerged):
                        break

                    oP = self.fReadRecord(oUP.iRID, oP.oMClass)

                except TypeError as tErr:
                    strMsg = "fAdd: [%s] [error] %s " % (strSOR, str(tErr))
                    self.oLog.fDebug(strMsg, 3)
                    self.oLog.fError(strMsg, 3)
                    raise tErr

                finally:
                    #
                    # Release RIDs so other matches can occur
                    # (assuming we're multithreaded)
                    #
                    self.oLog.fDebug('END fAdd: SOR = %s' % (strSOR), 5)
                    self.fReleaseMatchesMT(ctOrigMatches)

            # end while
            
            # after every transaction, read updated IDs:
            # can be optimized for only transactions that resulted with an update?
            oIDsP = self.fReadPersonIDs(oUP.iRID)

            return oUP, ctAllErasedP, oIDsP

    #------------------------------------------------------------------------
    #
    #  This method finds matches based on Golden Rule (in addition to
    #  matches found by the overridden fGetMatches method, which are
    #  based on primary keys)
    #
    #  Return: list of RIDs
    #
    #------------------------------------------------------------------------
    def fGetMatches(self, oP, strSOR):

        #
        # After calling fGetMatches in the parent class, we should
        # have all the matches by PK: those matches should not be
        # be run thru our filter..
        #
        # New assumptions we have to make:
        # Matches by PK should return either 0 or 1:
        # 0 implies action Create
        # 1 implies action Update (PK being USCID, which will
        #   translate to corresponding active USCID)
        # Anything else should be treated as error??
        #
        # SOR Update:
        # - must result in 1 match by PK
        # - any matches by GR will result in merge, so
        #   we must go thru filter
        #
        # SOR Create:
        # - must result in 0 match by PK
        # - 1 match by GR should be considered an
        #   update and allowed to go thru w/o filter
        # - multiple matches by GR will result in
        #   merge, so must go thru filter
        #
        strMatchesSR = ""
        ctRID2SOR = {}
        ctMatchesBySR = []
        ctMatchesByPK = []
        ctMatchesByGR = []
        
        ctMatchesByPK = TORInterface.fGetMatches(self, oP, strSOR)
        self.oLog.fDebug('TGPRInterface.fGetMatches (PR): %s' % (str(oP)), 5)
        
        iMatchesByPK = len(ctMatchesByPK)
        assert iMatchesByPK in [0,1], "Match by PK resulted in more than 1 match"

        strUSCID = oP.ctPKs.get('USCID', None)
        # match on basic IDs:
        ctAG_IDS = oP.ctAttrGroups.get(('IDs',), None)
        ctAG_DEMO = oP.ctAttrGroups.get(('Demo',), None)
        ctAG_Name_L = oP.ctAttrGroups.get(('Name', 'Verified'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'Reported'), [])
        ctAG_Name = ctAG_Name_L + ctAG_Name_R

        if ctAG_IDS and ctAG_DEMO and len(ctAG_Name) > 0:
            oSSN = ctAG_IDS[0].ctAttrs.get(('SSN',))
            oBD = ctAG_DEMO[0].ctAttrs.get(('BirthDate',))
            
            if (oSSN and oBD) and len(oSSN.strValue) > 0 and len(oBD.strValue) > 0:
                for oAGName in ctAG_Name:
                    oLast = oAGName.ctAttrs.get(('Last_STRP',))
                    oFirst = oAGName.ctAttrs.get(('First_STRP',))

                    if (oLast and oFirst) and len(oLast.strValue) > 0 and\
                           len(oFirst.strValue) > 0:

                        ctRes = self.oDB.fSelect(self.sqlSelectMatchesGR, [\
                            oSSN.strDBValue,
                            oBD.strDBValue,
                            oLast.strDBValue,
                            oFirst.strDBValue,
                            oAGName.oMGroup.iGroupID])

                        for (iRID,) in ctRes:
                            if iRID not in ctMatchesByGR:
                                ctMatchesByGR.append(iRID)

                        if (strUSCID is None) or (len(strUSCID) == 0):
                            ctResSR = self.oDB.fSelect(self.sqlSelectMatchesSR, [\
                                oBD.strDBValue,
                                oLast.strDBValue,
                                oFirst.strDBValue])
                        else:
                            ctResSR = self.oDB.fSelect(self.sqlSelectMatchesSRnotUSCID, [\
                                oBD.strDBValue,
                                oLast.strDBValue,
                                oFirst.strDBValue,
                                ("0-%s" % (strUSCID))])

                        for (iRID,) in ctResSR:
                            if iRID not in ctMatchesBySR:
                                ctMatchesBySR.append(iRID)

        for iRID in ctMatchesBySR:
            if iRID not in ctRID2SOR:
                ctRID2SOR[iRID] = []
            for sSOR in list(self.ctSORPKs.keys()):
                sPK = '%s_Value' % self.ctSORPKs[sSOR]
                iCnt = self.oDB.fSelect(self.sqlSelectSORCount % (sPK, sPK), [iRID])[0][0]
                if iCnt > 0:
                    if sSOR not in ctRID2SOR[iRID]:
                        ctRID2SOR[iRID].append(sSOR)
                        strMatchesSR += " %s - %s |" % (sSOR, iRID)

        if ctMatchesBySR and len(ctMatchesBySR) > 0:
            if (strUSCID is None) or (len(strUSCID) == 0):
                self.oSrLog.fDebug("[%s] Found Silver Rule Match for create request from SOR = %s to:%s" % (Logger.fGetLogTime(), strSOR, strMatchesSR))
            else:
                self.oSrLog.fDebug("[%s] Found Silver Rule Match for update request from SOR = %s with USCID = %s to:%s" % (Logger.fGetLogTime(), strSOR, strUSCID, strMatchesSR))

        self.oLog.fDebug("Found matches (PK): %s" % (str(ctMatchesByPK)), 5)
        self.oLog.fDebug("Found matches (GR): %s" % (str(ctMatchesByGR)), 5)

        ctMatches = []
        ctMatchesIntersect = ctMatchesByPK[:]
        for iRID in ctMatchesByGR:
            if iRID not in ctMatchesIntersect:
                ctMatchesIntersect.append(iRID)
        iTotalMatches = len(ctMatchesIntersect)
        if (iTotalMatches <= 1) or (self._fCanMergeMatches(ctMatchesByPK, ctMatchesIntersect, strSOR)):
            ctMatches = ctMatchesIntersect[:]
        else:
            ctMatches = ctMatchesByPK[:]

        self.oLog.fDebug("Found matches (filtered): %s" % (str(ctMatches)), 5)
        return ctMatches

    #------------------------------------------------------------------------
    #
    #  Args:
    #    ctMatchesByPK
    #    ctMatchesByGR
    #
    #  - Potential for merge if
    #    (ctMatchesByPK+ctMatchesByGR) > 1
    #  - In that case, check for SORs for all matched
    #    records (include SOR of incoming request)
    #  - If existence of unknown SOR, or more than 1
    #    record has the same SOR, then reject merge
    #
    #------------------------------------------------------------------------
    def _fCanMergeMatches(self, ctMatchesByPK, ctAllMatches, strSOR):
        # We don't want to merge VIP record with any other
        if strSOR == 'iVIP':
            return 0
        
        # This should've already been checked, so
        # is unnecessary...
        iTotalMatches = len(ctAllMatches)
        if iTotalMatches <= 1:
            return 1

        ctSOR2RID = {}
        ctRID2SOR = {}
        ctSOR2RID['UNKNOWN'] = (0, [])

        # If Update, store incoming request's SOR
        if len(ctMatchesByPK) > 0:
            iRID = ctMatchesByPK[0]
            ctSOR2RID[strSOR] = (1, [iRID])
            ctRID2SOR[iRID] = [strSOR]

        # Get list of SORs for the RID
        for iRID in ctAllMatches:
            if iRID not in ctRID2SOR:
                ctRID2SOR[iRID] = []
            for sSOR in list(self.ctSORPKs.keys()):
                sPK = '%s_Value' % self.ctSORPKs[sSOR]
                iCnt = self.oDB.fSelect(self.sqlSelectSORCount % (sPK, sPK), [iRID])[0][0]
                if iCnt > 0:
                    if sSOR not in ctRID2SOR[iRID]:
                        ctRID2SOR[iRID].append(sSOR)

        # Populate dict keyed by SOR
        for iRID in list(ctRID2SOR.keys()):
            ctSORs = ctRID2SOR[iRID]
            if len(ctSORs) == 0:
                ctSOR2RID['UNKNOWN'][1].append(iRID)
            else:
                for sSOR in ctSORs:
                    if sSOR not in ctSOR2RID:
                        ctSOR2RID[sSOR] = (1, [])
                    if iRID not in ctSOR2RID[sSOR][1]:
                        ctSOR2RID[sSOR][1].append(iRID)

        # Expect <=1 for valid SORs
        # Expect 0 for unknown SORs
        for sSOR in list(ctSOR2RID.keys()):
            iMax = ctSOR2RID[sSOR][0]
            iNum = len(ctSOR2RID[sSOR][1])
            if iNum > iMax:
                self.oLog.fDebug('\n=========================================\n', 5)
                self.oLog.fDebug('Discarding matches to avoid same-SOR merges: SOR=%s' % (strSOR), 5)
                self.oLog.fDebug('Time: [%s]\n\tMatches=%s\n\tSOR2RID: %s\tRID2SOR: %s' % (Logger.fGetLogTime(), str(ctAllMatches), str(ctSOR2RID), str(ctRID2SOR)), 5)
                self.oLog.fDebug('\n=========================================\n', 5)
                return 0

        return 1

    #------------------------------------------------------------------------
    #
    #  Merge into record with the given USCID
    #
    #  [X] To-Do: Change logic so that it only uses the given USCID if the
    #             sor is SIS, otherwise, call AutoMerge...
    #
    #------------------------------------------------------------------------
    def fSISHackMergeRecords(self, iRID1, iRID2, strSOR, strUSCID):
        #
        # Make sure this logic only applies if SOR is SIS (in addition to
        # it being an update, as opposed to create)
        #
        if strSOR != 'SIS' or (strUSCID is None) or (len(strUSCID) == 0):
            return self.fAutoMergeRecords(iRID1, iRID2, strSOR)

        oMClass = self.ctMClasses[('Person',)]
        oP = TObject(oMClass)
        oP.fAddPK('USCID', strUSCID, self.oEncrypt)

        ctMatches = self.fGetMatches(oP, strSOR)
        if len(ctMatches) == 0:
            raise ERepository(208, "Given USCID (%s) doesn't exist in DB for Merge" % \
                              (strUSCID))

        iRIDMatch = ctMatches[0]

        iRID1 = int(iRID1)
        iRID2 = int(iRID2)
        iRIDMatch = int(iRIDMatch)

        #
        # This part is confusing...
        # It seems that in general there is no reason that iRIDMatch
        # should be one of [iRID1, iRID2].
        # But since we have made sure that by getting this far, SOR must
        # have provided the USCID, and (first time round), iRID1 must be
        # the same as iRIDMatch.
        #
        
        if iRID1 == iRIDMatch:
            return self.fMergeRecords(iRID2, iRID1, strSOR, "Keep SIS record")
        elif iRID2 == iRIDMatch:
            return self.fMergeRecords(iRID1, iRID2, strSOR, "Keep SIS record")
        else:
            raise ERepository(208, "Given USCID (%s) doesn't match any Merge RID (%s and %s)." % \
                              (strUSCID, iRID1, iRID2))

    #------------------------------------------------------------------------
    #
    #  Uses auto logic to determine which record overrides the other.
    # 
    #------------------------------------------------------------------------
    def fAutoMergeRecords(self, iRID1, iRID2, strSOR):
        # merge into OLDER record  (smaller RID means older)
        # make it so that RID2 is oldest:
        if iRID1 < iRID2:
            x = iRID1
            iRID1 = iRID2
            iRID2 = x

        return self.fMergeRecords(iRID1, iRID2, strSOR, "Keep older record")

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fUSCID2RID(self, strUSCID, strSOR):
        # gather info on first USCID:
        oMClass = self.ctMClasses[('Person',)]
        oP = TObject(oMClass)
        oP.fAddPK('USCID', strUSCID, self.oEncrypt)
        ctMatches = TORInterface.fGetMatches(self, oP, strSOR)
        if len(ctMatches) != 1:
            raise ERepository(110, "Invalid USCID: %s" % (strUSCID))
        iRID = ctMatches[0]
        return iRID

    #------------------------------------------------------------------------
    #
    #  Users can specify two USCIDs that should never be merged.
    #
    #------------------------------------------------------------------------
    def fDoNotMergeRecordsExplicit(self, strUSCID1, strUSCID2, strSOR):
        
        self.oLog.fDebug('fDoNotMergeRecordsExplicit: oLockAdd Before Acquire', 5)
        self.oLockAdd.acquire()
        self.oLog.fDebug('fDoNotMergeRecordsExplicit: oLockAdd Acquired', 5)
        try:
            self.fConnect()

            iRID1 = self.fUSCID2RID(strUSCID1, strSOR)
            iRID2 = self.fUSCID2RID(strUSCID2, strSOR)

            if iRID1 == iRID2:
                raise ERepository(116, 'The two USCIDs point to the same record: %s, %s' % (strUSCID1, strUSCID2))

            iCount = self.oDB.fSelect(self.sqlCountDoNotMerge, [iRID1, iRID2, iRID2, iRID1])[0][0]
            if iCount > 0:
                return

            self.oDB.fExec(self.sqlInsertDoNotMerge, [iRID1, iRID2, 'GPR DoNotMerge %s' % (strSOR)])
            self.oDB.fExec(self.sqlInsertDoNotMerge, [iRID2, iRID1, 'GPR DoNotMerge %s' % (strSOR)])
            self.oDB.fCommit()
                
        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

        finally:
            self.oLog.fDebug('fDoNotMergeRecordsExplicit: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fDoNotMergeRecordsExplicit: oLockAdd Released', 5)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fUnmergeRecordsExplicit(self, strUSCID1, strUSCID2, strSOR):
        try:
            self.oLog.fDebug('Inside fUnmergeRecordsExplicit', 5)
            self.oLog.fDebug('fUnmergeRecordsExplicit: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()  # start lock
            self.oLog.fDebug('fUnmergeRecordsExplicit: oLockAdd Acquired', 5)
            self.fConnect()
            
            oMClass = self.ctMClasses[('Person',)]
            oP1 = TObject(oMClass)
            oP1.fAddPK('USCID', strUSCID1, self.oEncrypt)
            oP2 = TObject(oMClass)
            oP2.fAddPK('USCID', strUSCID2, self.oEncrypt)

            # make sure that the two are actually merged!
            # gather info on first USCID:
            ctRes = self.oDB.fSelect(self.sqlSelectUSCIDInfo, [oP1.ctEPKs['USCID']])
            if len(ctRes) == 0:
                raise ERepository(115, "SOR provided USCID that does not exist in PR: %s" % (strUSCID1))
            oP1.iRID = ctRes[0][0]
                                  
            # gather info on second USCID:
            ctRes = self.oDB.fSelect(self.sqlSelectUSCIDInfo, [oP2.ctEPKs['USCID']])
            if len(ctRes) == 0:
                raise ERepository(115, "SOR provided USCID that does not exist in PR: %s" % (strUSCID2))
            oP2.iRID = ctRes[0][0]

            iFinalRID1 = self.fUSCID2RID(strUSCID1, strSOR)
            # make sure the two IDs aren't identical:
            if iFinalRID1 != self.fUSCID2RID(strUSCID2, strSOR):
                raise ERepository(123, "Cannot unmerge two records that aren't already merged: %s, %s" % (strUSCID1, strUSCID2))

            if iFinalRID1 not in [oP1.iRID, oP2.iRID]:
                raise ERepository(123, "Cannot unmerge to records that aren't already merged to each-other: %s, %s" % (strUSCID1, strUSCID2))
            
            self.fUnmergeRecords(oP1, oP2, strSOR, "Explicit Unmerge")
            self.oDB.fCommit()

        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr
        
        finally:
            self.oLog.fDebug('fUnmergeRecordsExplicit: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fUnmergeRecordsExplicit: oLockAdd Released', 5)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fUnmergeRecords(self, oP1, oP2, strSOR, strNote = ''):
        # delete row from merge table
        sqlDelete = self.sqlDeleteMerge % (oP1.oMClass.strName)
        self.oDB.fExec(sqlDelete, [oP1.iRID, oP2.iRID])
        self.oDB.fExec(sqlDelete, [oP2.iRID, oP1.iRID])
        
        # delete information from records, leaving only shell ready for "Update"
        self.fClearRecordData(oP1)
        self.fClearRecordData(oP2)
        
        # set both as Active
        self.fSetActiveFlag(oP1, 'Y')
        self.fSetActiveFlag(oP2, 'Y')

    #------------------------------------------------------------------------
    #
    #  Given two USCIDs to merge, perform merge
    #
    #------------------------------------------------------------------------
    def fMergeRecordsExplicit(self, strUSCIDKeep, strUSCIDDiscard, strSOR):
        try:
            self.oLog.fDebug('Inside fMergeRecordsExplicit', 5)
            self.oLog.fDebug('fMergeRecordsExplicit: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()  # start lock
            self.oLog.fDebug('fMergeRecordsExplicit: oLockAdd Aqcuired', 5)
            self.fConnect()

            ctAllErasedP = []

            # SIS Requirement: Make sure that the one marked for keeps is ACTIVE
            self.oLog.fDebug('Ensure one record is marked Active', 5)
            self.fSetAsActiveUSCID(strUSCIDKeep, strSOR)

            # gather info on first USCID:
            self.oLog.fDebug('Get Info on the first record', 5)
            iRIDKeep = self.fUSCID2RID(strUSCIDKeep, strSOR)
                                  
            # gather info on second USCID:
            self.oLog.fDebug('Get Info on the second record', 5)
            iRIDDiscard = self.fUSCID2RID(strUSCIDDiscard, strSOR)

            # make sure the two IDs aren't identical:
            self.oLog.fDebug('Check if both USCIDs are different', 5)
            if strUSCIDKeep == strUSCIDDiscard:
                raise ERepository(116, "The two USCIDs point to the same record: %s, %s" % (strUSCIDKeep, strUSCIDDiscard))

            if iRIDKeep == iRIDDiscard:
                iRIDKept = iRIDKeep

            else:
                # proceed with the merge:
                (iRIDKept, oErasedP) = self.fMergeRecords(iRIDDiscard, iRIDKeep, strSOR, "Explicit Merge")
                ctAllErasedP.append(oErasedP)

                # check if now there is a GR match with any other records:
                # oNewP = self.fReadRecord(iRIDKept, self.ctMClasses[('Person',)])
                # ctOrigMatches = self.fGetMatchesMT(oP)

            self.oLog.fDebug('Call fReadRecord', 5)
            oP = self.fReadRecord(iRIDKept, self.ctMClasses[('Person',)])
            oUP = TObject(oP.oMClass)
            oUP.iRID = oP.iRID

            self.oLog.fDebug('Call fCheckMyAccess for Keep USCID', 5)
            self.fCheckMyAccess(iRIDKeep, False, 'Update')
            self.oLog.fDebug('Call fCheckMyAccess for Discard USCID', 5)
            self.fCheckMyAccess(iRIDDiscard, False, 'Update')

            self.oLog.fDebug('Call fAdd', 5)
            oUP, ctErasedP, oIDsP = self.fAdd(oP, strSOR, oUP = oUP, bAllowUpdates = 0)
            ctAllErasedP.extend(ctErasedP)

            self.oLog.fDebug('Call fCommit', 5)
            self.oDB.fCommit()

            return (oUP, ctAllErasedP, oIDsP)

        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

        finally:
            self.oLog.fDebug('fMergeRecordsExplicit: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fMergeRecordsExplicit: oLockAdd Released', 5)

    #------------------------------------------------------------------------
    #
    #  Given two RIDs & merge SOR (for record keeping) merge two
    #  records
    #
    #    iRID1: SOURCE Record  (DISCARD)
    #    iRID2: DESTINATION Record  (KEEP)
    #    return: record with attributes overwritten
    #
    #------------------------------------------------------------------------
    def fMergeRecords(self, iRID1, iRID2, strSOR, strNote = ''):
        self.oLog.fDebug('ENTERING fMergeRecords -------------------------', 5)
        self.oLog.fDebug('iRID1: %d, iRID2: %d, strSOR: %s' % (iRID1, iRID2, strSOR),5)

        # verify "DO-NOT-MERGE" table:
        self.oLog.fDebug('Check the record are in the "DO-NOT-MERGE" table', 5)
        iCount = self.oDB.fSelect(self.sqlCountDoNotMerge, [iRID1, iRID2, iRID2, iRID1])[0][0]
        if iCount > 0:
            self.oLog.fDebug('Raise an ERepository exception', 5)
            raise ERepository(104, 'Action would result in a merge of two DO-NOT-MERGE records.')

        # verify not a test record:
        self.oLog.fDebug('Check if the records are flagged as test records', 5)
        iCount = self.oDB.fSelect(self.sqlCountTestRecord, [iRID1, iRID2])[0][0]
        if iCount > 0:
            raise ERepository(104, 'Action would result in a merge of a record marked as a test person.')

        # read all the record (oR1)
        self.oLog.fDebug('Read all the record iRID1', 5)
        oMClass = self.ctMClasses[('Person',)]
        self.oLog.fDebug('About to read iRID1', 5)
        oR1 = self.fReadRecord(iRID1, oMClass)
        self.oLog.fDebug('oR1: %s' % (str(oR1)), 5)
        oR2 = TObject(oMClass)
        oR2.iRID = iRID2
        
        # update other record (oR2)
        self.oLog.fDebug('About to update iRID2:', 5)
        (oErasedP, bChanged) = self.fUpdateRecord(oR2, oR1, strSOR)

        # is this a hack?  return updated attributes with deleted record info?
        self.oLog.fDebug('The remaining....?', 5)
        self.fReadRecordShell(oErasedP, iRID1)
        
        # disable source record:
        self.oLog.fDebug('Disable source Record iRID1', 5)
        self.oDB.fExec(self.sqlUpdateAsMerged, ['GPR Merge [%s] %s' % (strSOR, strNote), oR1.iRID])

        # mark old merges that pointed to oR1 as now pointing to new record (oR2)
        self.oLog.fDebug('Mark old merge that pointed to iRID1 to point to iRID2', 5)
        self.oDB.fExec(self.sqlUpdateOldMerges, \
            [oR2.iRID, 'GPR Merge Update [%s] %s' % (strSOR, strNote), oR1.iRID])

        # update the do-not-merge settings to reflect new USCID situation.
        self.oLog.fDebug('Update the do-not-merge settings', 5)
        self.oDB.fExec(self.sqlUpdateOldDoNotMergesTemplate % {'RIDNUM': 1} , [iRID2, iRID1])
        self.oDB.fExec(self.sqlUpdateOldDoNotMergesTemplate % {'RIDNUM': 2} , [iRID2, iRID1])
       
        # created merged history field for oR1
        self.oLog.fDebug('Create merge history field for iRID1', 5)
        self.oDB.fExec(self.sqlInsertNewMerge,\
            [oR1.iRID, oR2.iRID, oR2.iRID, 'GPR Merge [%s] %s' % (strSOR, strNote)])

        self.oLog.fDebug('LEAVING fMergeRecords -------------------------', 5)
        return (oR2.iRID, oErasedP)

    #------------------------------------------------------------------------
    #
    #------------------------------------------------------------------------
    def fGetActiveUSCIDExplicit(self, oP, strSOR):
        try:
            self.oLog.fDebug('Inside fGetActiveUSCIDExplicit', 5)
            self.oLog.fDebug('fGetActiveUSCIDExplicit: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()  # start lock
            self.oLog.fDebug('fGetActiveUSCIDExplicit: oLockAdd Acquired', 5)
            self.fConnect()

            oP = self.fGetActiveUSCID(oP, strSOR)

            self.oDB.fCommit()

            return oP

        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

        finally:
            self.oLog.fDebug('fGetActiveUSCIDExplicit: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fGetActiveUSCIDExplicit: oLockAdd Released', 5)

    #------------------------------------------------------------------------
    #
    #  Get list of RIDs that matched on PKs plus the Golden Rule information.
    #
    #  If no matches are returned, then the USCID does not exist in the PR
    #  (or maybe it was not provided by SOR).
    #
    #  If more than one match is returned, then the records probably need
    #  to be merged, so we cannot decide which is active
    #
    #------------------------------------------------------------------------
    def fGetActiveUSCID(self, oP, strSOR):

        #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
        ctMatches = self.fGetMatchesMT(oP, strSOR,
                                       bException=1,
                                       strReqType='GetActiveUSCID')

        try:
            if len(ctMatches) != 1:
                raise ERepository(122, 'Request for USCID did not result in a single match; number of matches: %d' % (len(ctMatches)))

            oPU = oP.fCopyShell()
            self.fReadRecordShell(oPU, ctMatches[0])
            self.fReleaseMatchesMT(ctMatches)
            return oPU

        except ERepository as oErr:
            self.fReleaseMatchesMT(ctMatches)
            raise oErr

    #------------------------------------------------------------------------
    #
    #  Given RID, return TObject with IDs table having been read.
    #
    #------------------------------------------------------------------------
    def fReadPersonIDs(self, iRID):
        #self.oProf.fStartProfile('fReadPersonIDs')
        oIDsP = TObject(self.ctMClasses[('Person',)])  # contains IDs of updated record
        self.fReadRecordShell(oIDsP, iRID)
        self.fReadRecordMGroup(oIDsP, oIDsP.iRID, self.ctMClasses[('Person',)].ctMGroups[('IDs',)])
        #self.oProf.fStopProfile('fReadPersonIDs')
        return oIDsP

    #------------------------------------------------------------------------
    #
    #  Returns true/false if need to redo check for matches.
    #
    #  Notes:
    #  - key in general is one of:
    #    - (gname,) = oMGroup.fGetKey()
    #    - (gname, (dname,dvalue),...)
    #    - (gname, type)
    #    - (gname, type, (dname,dvalue),...)
    #  - since we're only dealing with GR data, none of which
    #    has dependencies, we're left with:
    #    - (gname,) = oMGroup.fGetKey()
    #    - (gname, type)
    #
    #------------------------------------------------------------------------
    def fCheckChangedGR(self, ctErased):
        ctChanged = {}
        for oP in ctErased:
            for ctGR in [('IDs', None, 'SSN', 1),
                         ('Demo', None, 'BirthDate', 2),
                         ('Name', 'Verified', 'First', 3),
                         ('Name', 'Verified', 'Last', 4),
                         ('Name', 'Reported', 'First', 3),
                         ('Name', 'Reported', 'Last', 4)]:
                (strG, strT, strA, iKey) = ctGR
                ctKey = (strG,)
                if strT:
                    ctKey = (strG, strT)
                if ctKey in oP.ctAttrGroups:
                    for oAG in oP.ctAttrGroups[ctKey]:
                        if (strA,) in oAG.ctAttrs:
                            ctChanged[iKey] = 1

        iNumChanged = len(ctChanged)
        #
        # No need to redo if nothing changed or EVERYTHING changed
        # (unless there has been a merge
        #
        # Notes:
        #   EVERYTHING changed means one of the following:
        #   1) it was a merge: this condition is taken care of in
        #      the calling function, so in this function we don't
        #      redo
        #   2) it was a create: obviously redoing will not result
        #      in more matches.
        #   3) it was an update: if everything changed it cannot
        #      now result in further matches otherwise it would
        #      not have been an update but a merge to begin with.
        #
        return (iNumChanged != 0) and (iNumChanged != 4)

    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Create a VIP record
    #
    #  How to flag a VIP record??
    #  - Use iVIPID
    #  - Maintain a table
    #
    #------------------------------------------------------------------------
    def fCreateVIPRecord(self, oP, strSOR, strMatchXML):
        #
        # We should be able to just use existing create logic.
        #
        (oPOutput, ctPErased, oIDsP) = self.fCreate(oP, strSOR)

        strRetXML = "%s<Person>\n<IDs>\n<USCID>%s</USCID>\n</IDs>\n</Person>\n"
        strRetXML %= (strMatchXML, '%s')
        strRetXML %= (oIDsP.ctPKs['USCID'])
        
        return (strRetXML, oIDsP.ctPKs['USCID'])
    
    #<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>
    #------------------------------------------------------------------------
    #
    #  Check presence of given attribute in a given object for a given
    #  attribute group.
    #
    #  Todo:
    #  Later to also take into account given type & multi-valued
    #  attributes
    #
    #------------------------------------------------------------------------
    def fCheckAttrPresence(self, oP, strAG, strAttr, strType=None, bIsMult=0):
        bFoundAttr = False
        ctAG = oP.ctAttrGroups.get((strAG,), None)
        if ctAG is not None:
            oAttr = ctAG[0].ctAttrs.get((strAttr,))
            if oAttr and len(oAttr.strValue) > 0:
                bFoundAttr = True

        return bFoundAttr

    #------------------------------------------------------------------------
    #
    #  Update data that is external to Person attributes
    #  e.g. SIS Term table
    #
    #------------------------------------------------------------------------
    def fUpdateSORData(self, oInput, strSOR, strAction, strObject):
        #
        # Figure out which utility class/method to call
        # e.g. self.oSISUtil.fUpdateTermTable(oInput)
        #
        oFunc = 'self.o%(SOR)sUtil.fUpdate%(Object)s' % {'SOR':strSOR,
                                                         'Object':strObject}

        self.oLog.fDebug('fUpdateSORData: %s: %s' % (strSOR, strObject), 5)
        #self.oProf.fStartProfile('fUpdateSORData')
        self.fSetup()

        try:
            self.oLog.fDebug('fUpdateSORData: oLockAdd Before Acquire', 5)
            self.oLockAdd.acquire()
            self.oLog.fDebug('fUpdateSORData: oLockAdd Acquired', 5)
            self.fConnect()

            ctRes = eval(oFunc)(oInput, self.oDB)

            self.oDB.fCommit()

            return ctRes
        
        except ERepository as oErr:
            self.oDB.fRollback()
            raise oErr

        finally:
            self.oLog.fDebug('fUpdateSORData: oLockAdd Before Release', 5)
            self.oLockAdd.release()
            self.oLog.fDebug('fUpdateSORData: oLockAdd Released', 5)
            #self.oProf.fStopProfile('fUpdateSORData')


    #------------------------------------------------------------------------
    #
    #  For testing only...
    #
    #------------------------------------------------------------------------
    def fGetTermDates(self):
        return self.oSISUtil.fGetTermDates(self.oDB)

    #------------------------------------------------------------------------
    #    
    #  Get current term...
    #
    #------------------------------------------------------------------------
    def fGetCurrentTerm(self):
        return self.oSISUtil.fGetCurrentTerm(self.oDB)

    
#****************************************************************************
#
#  Following classes provide ways to deal with SOR-specific data
#  that is part of the PR database but external to OR/GPR objects:
#  purpose of this data is to be able to make certain decisions
#  about the OR/GPR objects data.
#
#  Initial XML request should be processed through XMLParse method,
#  as with all transactions. If requested action is for manipulating
#  SOR-specific data then these utility classes should take over from
#  that point.
#
#  Notes:
#    Database setup assumed done in class that makes use of this
#    utility class.
#
#  Todo:
#  [] need ability to use oGPR's db setup.
#
#****************************************************************************

class TSORUtil(object):
    _strName = 'SOR'
    _ctValidObjects = []
    
    _sqlInsert = """
    insert into %s_%s_%s
    (ID,CREATE_DTM,MODIFIED_DTM,%s)
    values
    (SEQ_IDS.nextval,sysdate,sysdate,%s)
    """

    _sqlUpdate = """
    update %s_%s_%s
    set MODIFIED_DTM=sysdate, %s
    where %s
    """

    _sqlSelect = """
    select %s
    from %s_%s_%s
    where %s
    """

    def __init__(self, strSOR, oLog, oProf):
        self._strSOR = strSOR
        
        self._oLog = oLog
        self._oProf = oProf
        self._oDB = None # get this as needed

        #
        # Maintain a list of tables that can be updated
        # by the SOR
        #
        self._ctValidTables = []

    def _fSelect(self, strType, strCols, strParams):
        self._oLog.fDebug('---------- Inside _fSelect ----------', 5)
        strKeys = strParams[0]
        ctVals = strParams[1]
        sqlCmd = self._sqlSelect % (strCols,
                                    TSORUtil._strName,
                                    self._strSOR,
                                    strType,
                                    strKeys)
        return self._oDB.fSelect(sqlCmd, ctVals)

    def _fUpdate(self, strType, ctUpdParams, ctSrchParams):
        self._oLog.fDebug('---------- Inside _fUpdate ----------', 5)
        strCols = ctUpdParams[0]
        ctVals = ctUpdParams[1]
        strKeys = ctSrchParams[0]
        ctVals += ctSrchParams[1]
        sqlCmd = self._sqlUpdate % (TSORUtil._strName,
                                    self._strSOR,
                                    strType,
                                    strCols,
                                    strKeys)
        self._oLog.fDebug('---------- SQL Command: %s ----------' % sqlCmd, 5)
        self._oDB.fExec(sqlCmd, ctVals)
        return

    def _fInsert(self, strType, ctInsParams):
        self._oLog.fDebug('---------- Inside _fInsert ----------', 5)
        strCols = ctInsParams[0]
        strBindVars = ctInsParams[1]
        ctVals = ctInsParams[2]
        sqlCmd = self._sqlInsert % (TSORUtil._strName,
                                    self._strSOR,
                                    strType,
                                    strCols,
                                    strBindVars)
        self._oDB.fExec(sqlCmd, ctVals)
        return

    def _fGetTable(self, strObj):
        pass

    def _fConstructValidTables(self):
        pass

class TSISUtil(TSORUtil):
    _strName = 'SIS'
    _ctValidObjects = ['TERM','MAJOR']
    
    def __init__(self, oLog, oProf):
        TSORUtil.__init__(self, self._strName, oLog, oProf)

        self._fConstructValidTables()

        self._oLog = oLog
        #
        # Cache results of current term
        #
        self._oToday = None
        self._oTermCache = {}

    ##def __del__(self):
    ##    TSORUtil.__del__(self)

    #
    # Public interface
    #

    # Update the SOR_SIS_TERM table
    #
    # Example XML:
    # <UpdateTable>
    #    <TermTable>
    #       <TermData TermCode="20111">
    #          <Note>Manual xml update testing</Note>
    #          <TermDesc>Spring 2011</TermDesc>
    #          <PreRegBegDate>10/25/2010</PreRegBegDate>
    #          <RegBegDate>01/03/2011</RegBegDate>
    #          <RegEndDate>01/07/2011</RegEndDate>
    #          <ClassBegDate>01/10/2011</ClassBegDate>
    #          <TermEndDate>05/06/2011</TermEndDate>
    #          <CommencementDate>05/13/2011</CommencementDate>
    #       </TermData>
    #    </TermTable>
    # </UpdateTable>
    def fUpdateTermTable(self, oTerm, oDB):
        strType = "Term"

        self._oDB = oDB

        strTbl = self._fGetTable(strType)
        if strTbl not in self._ctValidTables:
            strErr = "%s cannot update given table: %s" % \
                     (self._strName, strType)
            raise ERepository(125, strErr)

        #
        # parse xml to get key-value pairs
        #

        ctTerm = self._fParseTermXML(oTerm)

        #
        # using parsed results, update table
        #

        ctRes = self._fUpdateTermTable(strType, ctTerm)

        #
        # format response as portion of XML doc
        # (include terms processed)
        #

        strXMLTerms = ''
        strXMLTempl = '<TermCode>%s</TermCode>'
        for sTerm in ctRes:
            if strXMLTerms:
                strXMLTerms += '\n'
            strXMLTerms += strXMLTempl % sTerm

        return (strXMLTerms, ctRes)
    
    # Update the SOR_SIS_MAJOR table
    #
    # Example XML:
    # <UpdateTable>
    #    <MajorTable>
    #       <MajorData>
    #         <POStCode>999</POStCode>
    #         ...
    #       </MajorData>
    #    </MajorTable>
    # </UpdateTable>
    def fUpdateMajorTable(self, oMajor, oDB):
        strType = "Major"
        self._oDB = oDB

        self._oLog.fDebug('Inside fUpdateMajorTable', 5)
        strTbl = self._fGetTable(strType)
        self._oLog.fDebug('********** Table Name: %s **********' % strTbl, 5)
        if strTbl not in self._ctValidTables:
            strErr = "%s cannot update given table: %s" % \
                     (self._strName, strType)
            raise ERepository(125, strErr)

        #
        # parse xml to get key-value pairs
        #

        self._oLog.fDebug('Before fParseMajorXML', 5)
        ctMajor = self._fParseMajorXML(oMajor)
        self._oLog.fDebug('After fParseMajorXML', 5)

        #
        # using parsed results, update table
        #

        self._oLog.fDebug('Before fUpdateMajorTable', 5)
        ctRes = self._fUpdateMajorTable(strType, ctMajor)
        self._oLog.fDebug('After fUpdateMajorTable', 5)

        #
        # format response as portion of XML doc
        # (include terms processed)
        #

        self._oLog.fDebug('fUpdateMajorTable: %s' % (ctRes), 5)
        strXMLPOStCode = ''
        strXMLPOStCodeTemplate = '<POStCode>%s</POStCode>'
        for sPOStCode in ctRes:
            if strXMLPOStCode:
                strXMLPOStCode += '\n'
            strXMLPOStCode += strXMLPOStCodeTemplate % sPOStCode

        self._oLog.fDebug('END fUpdateMajorTable', 5)
        return (strXMLPOStCode, ctRes)
    
    def fGetCurrentTerm(self, oDB, bWithAdjTerms=0):
        self._oDB = oDB

        self._fUpdateTermCache()

        if bWithAdjTerms:
            return (self._oTermCache['current'],
                    self._oTermCache['next'],
                    self._oTermCache['previous'])
        else:
            return self._oTermCache['current']

    def fGetPreviousTerm(self, oDB):
        self._oDB = oDB

        self._fUpdateTermCache()

        return self._oTermCache['previous']

    def fGetNextTerm(self, oDB):
        self._oDB = oDB

        self._fUpdateTermCache()

        return self._oTermCache['next']

    def fGetNextNextTerm(self, oDB):
        self._oDB = oDB

        self._fUpdateTermCache()

        return self._oTermCache['nextnext']

    def fGetTermDates(self, oDB):
        self._oDB = oDB

        return self.__fGetTermDates()

    #
    # Private interface
    #

    def _fParseTermXML(self, oTerm):
        ctTermRows = []

        for oTermCode in oTerm.childNodes:
            ctTermRow = {}
            
            if oTermCode.nodeName == '#text':
                continue
            
            if len(list(oTermCode.attributes.values())) == 0:
                strErr = "Expected 'TermCode' attribute, instead found nothing"
                raise ERepository(125, strErr)
            
            if list(oTermCode.attributes.values())[0].name != "TermCode":
                strErr = "Expected 'TermCode' attribute, instead found '%s'" % \
                         list(oTermCode.attributes.values())[0].name
                raise ERepository(125, strErr)
            
            if list(oTermCode.attributes.values())[0].value == "":
                strErr = "Missing value for 'TermCode'"
                raise ERepository(125, strErr)
            
            ctTermRow[list(oTermCode.attributes.values())[0].name] = list(oTermCode.attributes.values())[0].value
            
            if oTermCode.hasChildNodes:
                for oTermField in oTermCode.childNodes:
                    
                    if oTermField.nodeName == '#text':
                        continue
                    
                    if oTermField.hasChildNodes:
                        if len(oTermField.childNodes) > 0:
                            ctTermRow[oTermField.nodeName] = (oTermField.childNodes[0].data).strip()
                        else:
                            ctTermRow[oTermField.nodeName] = ''
                            
                    else:
                        ctTermRow[oTermField.nodeName] = ''
                        
            ctTermRows.append(ctTermRow)

        return ctTermRows

    def _fParseMajorXML(self, oMajor):
        ctMajorsRows = []

        for oMajor in oMajor.childNodes:
            ctMajorRow = {}
            
            if oMajor.nodeName == '#text':
                continue
            
            if oMajor.hasChildNodes:
                for oMajorField in oMajor.childNodes:
                    
                    if oMajorField.nodeName == '#text':
                        continue

                    if oMajorField.hasChildNodes:
                        if len(oMajorField.childNodes) > 0:
                            ctMajorRow[oMajorField.nodeName] = (oMajorField.childNodes[0].data).strip()
                        else:
                            ctMajorRow[oMajorField.nodeName] = ''
                            
                    else:
                        ctMajorRow[oMajorField.nodeName] = ''
                        
            ctMajorsRows.append(ctMajorRow)

        return ctMajorsRows

    def _fParseMinorXML(self, oMinor):
        pass

    def _fParseYearXML(self, oMinor):
        pass

    def _fUpdateTermTable(self, strType, ctTerm):
        """ Make sure to convert from unicode to ascii

        Database utility only handles ASCII...
        
        """
        ctSuccess = []
        for cRow in ctTerm:
            strTermCode = str(cRow['TermCode'])
            strCol = 'count(*)'
            strParams = ('TermCode = ?', [strTermCode])
            ctRes = self._fSelect(strType, strCol, strParams)
            if len(ctRes) == 0 or len(ctRes[0]) == 0 or int(ctRes[0][0]) == 0:
                # insert
                ctInsParams = ()
                ctCols = []
                ctVals = []
                ctBindVars = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    ctCols.append(sCol)
                    ctBindVars.append('?')
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                strBindVars = ','.join(ctBindVars)
                ctInsParams = (strCols, strBindVars, ctVals)
                self._fInsert(strType, ctInsParams)
                ctSuccess.append(strTermCode)
            elif int(ctRes[0][0]) == 1:
                # update
                ctUpdParams = ctSrchParams = ()
                ctCols = []
                ctVals = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    if sCol == 'TermCode':
                        continue
                    sCol = '%s = ?' % sCol
                    ctCols.append(sCol)
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                ctUpdParams = (strCols, ctVals)
                ctSrchParams = ('TermCode = ?', [strTermCode])
                self._fUpdate(strType, ctUpdParams, ctSrchParams)
                ctSuccess.append(strTermCode)
            else:
                # error
                strErr = "Found multiple instances of same term (TermCode=%s)" % \
                         strTermCode
                raise ERepository(125, strErr)
        return ctSuccess

    def _fUpdateMajorTable(self, strType, ctMajor):
        # Make sure to convert from unicode to ascii
        # Database utility only handles ASCII...
        
        self._oLog.fDebug('========== Inside _fUpdateMajorTable ==========', 5)
        ctSuccess = []
        for cRow in ctMajor:
            strPOStCode = str(cRow['POStCode'])
            strCol = 'count(*)'
            strParams = ('POStCode = ?', [strPOStCode])
            ctRes = self._fSelect(strType, strCol, strParams)
            if len(ctRes) == 0 or len(ctRes[0]) == 0 or int(ctRes[0][0]) == 0:
                self._oLog.fDebug('++++++++++ Inside _fUpdateMajorTable INSERT ++++++++++', 5)
                # insert
                ctInsParams = ()
                ctCols = []
                ctVals = []
                ctBindVars = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    ctCols.append(sCol)
                    ctBindVars.append('?')
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                strBindVars = ','.join(ctBindVars)
                ctInsParams = (strCols, strBindVars, ctVals)
                self._fInsert(strType, ctInsParams)
                ctSuccess.append(strPOStCode)
            elif int(ctRes[0][0]) == 1:
                self._oLog.fDebug('++++++++++ Inside _fUpdateMajorTable UPDATE ++++++++++', 5)
                # update
                ctUpdParams = ctSrchParams = ()
                ctCols = []
                ctVals = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    if sCol == 'POStCode':
                        continue
                    sCol = '%s = ?' % sCol
                    ctCols.append(sCol)
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                ctUpdParams = (strCols, ctVals)
                ctSrchParams = ('POStCode = ?', [strPOStCode])
                self._fUpdate(strType, ctUpdParams, ctSrchParams)
                ctSuccess.append(strPOStCode)
            else:
                # error -- impossible because MajorID is primary key
                strErr = "Found multiple instances of same POStCode (POStCode=%s)" % strPOStCode
                raise ERepository(125, strErr)
        return ctSuccess

    def _fUpdateMinorTable(self, ctMinor):
        pass

    def _fUpdateYearTable(self, ctYear):
        pass

    def _fInitTermCache(self):
        pass
    
    def _fUpdateTermCache(self):
        oToday = datetime.datetime.today().date()

        if self._oToday != oToday:
            self._fComputeTerms(oToday)
            self._oToday = oToday

    def _fComputeTerms(self, oToday):
        """ Will use RegBegDate to decide current term

        Need to compute cols as follows:
        TermCode
        BeginDate
        EndDate
        PreviousTermCode
        NextTermTermCode

        Save results in dict:
        TermCache[TermCode] = [BeginDate, EndDate, PreviousTermCode, NextTermTermCode]
        
        """

        strType = "Term"
        strTable = self._fGetTable(strType)

        strCols = 'TermCode, RegBegDate'

        sqlSelectTerms = """
          select %s from %s
          """

        sqlSelectTerms = sqlSelectTerms % (strCols, strTable)
        
        BEGIN_DATE,END_DATE,PREVIOUS_TERMCODE,NEXT_TERMCODE,NEXT_NEXT_TERMCODE = list(range(5))

        strDateFmt = '%m/%d/%Y'

        oTermData = {}
        for (strTerm, strDate) in self._oDB.fSelect(sqlSelectTerms):
            ctDate = time.strptime(strDate, strDateFmt)
            oDate = datetime.date(ctDate[0],ctDate[1],ctDate[2])
            # self._oLog.fDebug('Term: ' + strTerm + ' Date: ' + str(oDate), 5)
            oTermData[strTerm] = [oDate, None, None, None, None]

        ctTermsSort = []
        ctTermsMap = {}
        ctTmp = list(oTermData.keys())
        for sT in ctTmp:
            iT = int(sT)
            ctTermsSort.append(iT)
            ctTermsMap[iT] = sT
        ctTermsSort.sort()
        del ctTmp

        iNumTerms = len(ctTermsSort)
        iRange = list(range(iNumTerms))
        for i in iRange:
            sCurrKey = ctTermsMap[ctTermsSort[i]]
            self._oLog.fDebug('Current Key: ' + sCurrKey, 5)
            self._oLog.fDebug('Current Term: ' + str(ctTermsSort[i]), 5)

            if i != 0 and i < iNumTerms:
                sPrevKey = ctTermsMap[ctTermsSort[i-1]]
                oTermData[sCurrKey][PREVIOUS_TERMCODE] = sPrevKey
                self._oLog.fDebug('Previous Term: ' + str(ctTermsSort[i-1]), 5)

            if i < iNumTerms-1:
                sNextKey = ctTermsMap[ctTermsSort[i+1]]
                oTermData[sCurrKey][NEXT_TERMCODE] = sNextKey
                #
                # Calculate current term's end date
                #
                oNextBegDate = oTermData[sNextKey][BEGIN_DATE]
                oTermData[sCurrKey][END_DATE] = oNextBegDate - datetime.timedelta(1)
                self._oLog.fDebug('Next Term: ' + str(ctTermsSort[i+1]), 5)

            if i < iNumTerms-2:
                sNextNextKey = ctTermsMap[ctTermsSort[i+2]]
                oTermData[sCurrKey][NEXT_NEXT_TERMCODE] = sNextNextKey
                self._oLog.fDebug('NextNext Term: ' + str(ctTermsSort[i+2]), 5)

        #
        # Now we're set to determine current, previous, next, and next next terms
        #

        self._oTermCache.clear()
        _ctCurr = []
        
        for strTerm in list(ctTermsMap.values()):
            if oToday >= oTermData[strTerm][BEGIN_DATE] \
               and oToday <= oTermData[strTerm][END_DATE]:
                _ctCurr.append(strTerm)

        strErr = "Error while computing current term: "

        if len(_ctCurr) == 0:
            strErr = strErr + \
                     "Unable to determine current term from %s" % \
                     strTable
            raise ERepository(126, strErr)

        if len(_ctCurr) > 1:
            strErr = strErr + \
                     "Multiple terms in %s qualify for current term: %s" % \
                     (strTable, str(_ctCurr))
            raise ERepository(126, strErr)

        strCurr = _ctCurr[0]
        strPrev = oTermData[strCurr][PREVIOUS_TERMCODE]
        strNext = oTermData[strCurr][NEXT_TERMCODE]
        strNextNext = oTermData[strCurr][NEXT_NEXT_TERMCODE]

        #
        # Make sure terms we ended up with make sense
        #
        # e.g. if current term is 20061 i.e. year 2006, term 1
        # then we expect previous term to be year 2005, term 3
        # and we expect next term to be year 2006, term 2
        #
        # Assumptions: 4-digit year, 1-digit termcode
        #

        iCurrTermPrefix = int(strCurr[:-1])
        iCurrTermSuffix = int(strCurr[-1])

        if strPrev is not None:
            iPrevTermPrefix = int(strPrev[:-1])
            iPrevTermSuffix = int(strPrev[-1])

            iExpectTermPrefix = iCurrTermPrefix
            iExpectTermSuffix = iCurrTermSuffix-1
            if iExpectTermSuffix <= 0:
                iExpectTermPrefix -= 1
                iExpectTermSuffix = 3

            strGot = str(iPrevTermPrefix) + str(iPrevTermSuffix)
            strExpect = str(iExpectTermPrefix) + str(iExpectTermSuffix)

            if strGot != strExpect:
                strErr = "Computed previous term does not match expected " \
                         "previous term (GOT: %s, EXPECT: %s)" % \
                         (strGot, strExpect)
                raise  ERepository(126, strErr)

        if strNext is not None:
            iNextTermPrefix = int(strNext[:-1])
            iNextTermSuffix = int(strNext[-1])

            iExpectTermPrefix = iCurrTermPrefix
            iExpectTermSuffix = iCurrTermSuffix+1
            if iExpectTermSuffix >= 4:
                iExpectTermPrefix += 1
                iExpectTermSuffix = 1

            strGot = str(iNextTermPrefix) + str(iNextTermSuffix)
            strExpect = str(iExpectTermPrefix) + str(iExpectTermSuffix)

            if strGot != strExpect:
                strErr = "Computed next term does not match expected " \
                         "next term (GOT: %s, EXPECT: %s)" % \
                         (strGot, strExpect)
                raise  ERepository(126, strErr)

        if strNextNext is not None:
            iNextTermPrefix = int(strNextNext[:-1])
            iNextTermSuffix = int(strNextNext[-1])

            iExpectTermPrefix = iCurrTermPrefix
            iExpectTermSuffix = iCurrTermSuffix+2
            if iExpectTermSuffix == 4:
                iExpectTermPrefix += 1
                iExpectTermSuffix = 1
            elif iExpectTermSuffix >= 5:
                iExpectTermPrefix += 1
                iExpectTermSuffix = 2

            strGot = str(iNextTermPrefix) + str(iNextTermSuffix)
            strExpect = str(iExpectTermPrefix) + str(iExpectTermSuffix)

            if strGot != strExpect:
                strErr = "Computed next term does not match expected " \
                         "next term (GOT: %s, EXPECT: %s)" % \
                         (strGot, strExpect)
                raise  ERepository(126, strErr)


        #
        # All OK, so cache...
        #
        
        self._oTermCache['current'] = strCurr
        self._oTermCache['previous'] = strPrev
        self._oTermCache['next'] = strNext
        self._oTermCache['nextnext'] = strNextNext

        return

    def __fGetTermDates(self):
        """ For temporary use..

        Get a table of terms and start/end dates.
        
        """
        
        _TERM_TO_START_FROM_ = 20061
        
        strType = "Term"
        strTable = self._fGetTable(strType)

        strCols = 'TermCode, RegBegDate'

        sqlSelectTerms = """
          select %s from %s
          """

        sqlSelectTerms = sqlSelectTerms % (strCols, strTable)
        
        BEGIN_DATE,END_DATE,PREVIOUS_TERMCODE,NEXT_TERMCODE = list(range(4))

        strDateFmt = '%m/%d/%Y'

        oTermData = {}
        for (strTerm, strDate) in self._oDB.fSelect(sqlSelectTerms):
            ctDate = time.strptime(strDate, strDateFmt)
            oDate = datetime.date(ctDate[0],ctDate[1],ctDate[2])
            oTermData[strTerm] = [oDate, None, None, None]

        ctTermsSort = []
        ctTermsMap = {}
        ctTmp = list(oTermData.keys())
        for sT in ctTmp:
            iT = int(sT)
            ctTermsSort.append(iT)
            ctTermsMap[iT] = sT
        ctTermsSort.sort()
        del ctTmp

        iNumTerms = len(ctTermsSort)
        iRange = list(range(iNumTerms))
        for i in iRange:
            sCurrKey = ctTermsMap[ctTermsSort[i]]

            if i != 0:
                sPrevKey = ctTermsMap[ctTermsSort[i-1]]
                oTermData[sCurrKey][PREVIOUS_TERMCODE] = sPrevKey

            if i != iNumTerms-1:
                sNextKey = ctTermsMap[ctTermsSort[i+1]]
                oTermData[sCurrKey][NEXT_TERMCODE] = sNextKey

                #
                # Calculate current term's end date
                #
                oNextBegDate = oTermData[sNextKey][BEGIN_DATE]
                oTermData[sCurrKey][END_DATE] = oNextBegDate - datetime.timedelta(1)

        #
        # Now build a string with:
        #     TermCode | StartDate | EndDate
        #
        sTermDates = 'TermCode   |   TermBegin   |   TermEnd\n'
        for iTerm in ctTermsSort:
            if iTerm >= _TERM_TO_START_FROM_:
                sTerm = ctTermsMap[iTerm]
                sTermDates += '%s   |   %s   |   %s\n' % (sTerm, oTermData[sTerm][BEGIN_DATE], oTermData[sTerm][END_DATE])
        
        return sTermDates
    
    def __NOTUSED__fComputeCurrTerm(self):
        sqlSelectCurrTerm = """
          select %s from %s
          where to_date(%s, 'MM/DD/YYYY') < sysdate
          and to_date(%s, 'MM/DD/YYYY') > sysdate
          """

        strType = "Term"
        strTable = self._fGetTable(strType)

        strBegin = 'RegBegDate'
        strEnd   = 'TermEndDate'
        strField = 'TermCode'

        ctTerms = []
        sqlSelectCurrTerm = sqlSelectCurrTerm % (strField, strTable,
                                                 strBegin, strEnd)
        
        for (strTerm,) in self._oDB.fSelect(sqlSelectCurrTerm):
            ctTerms.append(strTerm)

        strErr = "Error while computing current term: "

        if len(ctTerms) == 0:
            strErr = strErr + \
                     "No rows selected from %s" % \
                     strTable
            raise ERepository(126, strErr)

        if len(ctTerms) > 1:
            strErr = strErr + \
                     "More than 1 row selected from %s" % \
                     strTable
            raise ERepository(126, strErr)

        return ctTerms[0]

    def _fGetTable(self, strObj):
        strObj = strObj.upper()
        return '%s_%s_%s' % (TSORUtil._strName,
                             self._strName,
                             strObj)
        
    def _fConstructValidTables(self):
        for strObj in self._ctValidObjects:
            strTbl = '%s_%s_%s' % (TSORUtil._strName,
                                   self._strName,
                                   strObj)
            self._ctValidTables.append(strTbl)


#****************************************************************************
#
#  Class: PPBS update/insert Department data
#
#****************************************************************************

class TPPBSUtil(TSORUtil):
    _strName = 'PPBS'
    _ctValidObjects = ['DEPT']
    _oLog = None
    
    def __init__(self, oLog, oProf):
        TSORUtil.__init__(self, self._strName, oLog, oProf)
        self._fConstructValidTables()
        self._oLog = oLog


    #
    # Public interface
    #

    # Update the SOR_PPBS_DEPT table
    #
    # Example XML:
    #    <UpdateTable>
    #        <DeptTable>
    #            <DeptData>
    #                <Department_Code>0610210000</Department_Code>
    #                <Active_Flag>Y</Active_Flag>
    #                <Department_Name>Enterprise Middleware Applications</Department_Name>
    #                <Directory_Department_Name/>
    #                <Division_Code>0610</Division_Code>
    #                <Division_Name>Information Technology Services</Division_Name>
    #                <Directory_Division_Name/>
    #                <Coord_RID>0066717</Coord_RID>
    #                <Coord_Email>rharriso@usc.edu</Coord_Email>
    #                <TA_Code>T01</TA_Code>
    #                <TA_Contact_RID>0066717</TA_Contact_RID>
    #                <TA_Contact_Email>rharriso@usc.edu</TA_Contact_Email>
    #                <Student_Template>WP</Student_Template>
    #                <Non_Exempt_Template>WP</Non_Exempt_Template>
    #                <Exempt_Template>EX</Exempt_Template>
    #                <Print_Leave>N</Print_Leave>
    #            </DeptData>
    #        </DeptTable>
    #    </UpdateTable>

    def fUpdateDeptTable(self, oDepts, oDB):
        strType = "Dept"

        self._oDB = oDB

        strTbl = self._fGetTable(strType)
        if strTbl not in self._ctValidTables:
            strErr = "%s cannot update given table: %s" % \
                     (self._strName, strType)
            raise ERepository(125, strErr)

        #
        # parse xml to get key-value pairs
        #

        ctDepts = self._fParseDeptXML(oDepts)

        #
        # using parsed results, update table
        #

        ctRes = self._fUpdateDeptTable(strType, ctDepts)

        #
        # format response as portion of XML doc
        # (include DeptCodes processed)
        #

        strXMLDeptCode = ''
        strXMLTempl = '<Department_Code>%s</Department_Code>'
        for sDeptCode in ctRes:
            if strXMLDeptCode:
                strXMLDeptCode += '\n'
            strXMLDeptCode += strXMLTempl % sDeptCode

        return (strXMLDeptCode, ctRes)
    
    #
    # Private interface
    #

    def _fParseDeptXML(self, oDepts):
        ctDeptRows = []

        for oDept in oDepts.childNodes:
            ctDeptRow = {}
            
            if oDept.nodeName == '#text':
                continue
            
            if oDept.hasChildNodes:
                for oDeptField in oDept.childNodes:
                    
                    if oDeptField.nodeName == '#text':
                        continue

                    if oDeptField.hasChildNodes:
                        if len(oDeptField.childNodes) > 0:
                            ctDeptRow[oDeptField.nodeName] = (oDeptField.childNodes[0].data).strip()
                        else:
                            ctDeptRow[oDeptField.nodeName] = ''
                            
                    else:
                        ctDeptRow[oDeptField.nodeName] = ''
                        
            ctDeptRows.append(ctDeptRow)

        return ctDeptRows

    def _fUpdateDeptTable(self, strType, ctDepts):
        """ Make sure to convert from unicode to ascii

        Database utility only handles ASCII...
        
        """
        ctSuccess = []
        for cRow in ctDepts:
            strDeptCode = str(cRow['Department_Code'])
            strCol = 'count(*)'
            strParams = ('Department_Code = ?', [strDeptCode])
            ctRes = self._fSelect(strType, strCol, strParams)
            if len(ctRes) == 0 or len(ctRes[0]) == 0 or int(ctRes[0][0]) == 0:
                # insert
                ctInsParams = ()
                ctCols = []
                ctVals = []
                ctBindVars = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    ctCols.append(sCol)
                    ctBindVars.append('?')
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                strBindVars = ','.join(ctBindVars)
                ctInsParams = (strCols, strBindVars, ctVals)
                self._fInsert(strType, ctInsParams)
                ctSuccess.append(strDeptCode)
            elif int(ctRes[0][0]) == 1:
                # update
                bUpdateNeeded = self._fCompareRows(strType, cRow)
                if bUpdateNeeded:
                    ctUpdParams = ctSrchParams = ()
                    ctCols = []
                    ctVals = []
                    for sCol, sVal in list(cRow.items()):
                        sCol = str(sCol)
                        sVal = str(sVal)
                        if sCol == 'Department_Code':
                            continue
                        sCol = '%s = ?' % sCol
                        ctCols.append(sCol)
                        ctVals.append(sVal)
                    strCols = ','.join(ctCols)
                    ctUpdParams = (strCols, ctVals)
                    ctSrchParams = ('Department_Code = ?', [strDeptCode])
                    self._fUpdate(strType, ctUpdParams, ctSrchParams)
                ctSuccess.append(strDeptCode)
            else:
                # error -- impossible because Department_Code is unique key
                strErr = "Found multiple instances of same Department Code (Department_Code=%s)" % \
                         strDeptCode
                raise ERepository(125, strErr)
        return ctSuccess

    def _fGetTable(self, strObj):
        strObj = strObj.upper()
        return '%s_%s_%s' % (TSORUtil._strName,
                             self._strName,
                             strObj)

    def _fConstructValidTables(self):
        for strObj in self._ctValidObjects:
            strTbl = '%s_%s_%s' % (TSORUtil._strName,
                                   self._strName,
                                   strObj)
            self._ctValidTables.append(strTbl)

    def _fCompareRows(self, strType, cNewRow):
        strDeptCode = str(cNewRow['Department_Code'])
        dictColNames = ('Department_Code','Active_Flag','Department_Name','Directory_Department_Name','Division_Code', \
                        'Division_Name','Directory_Division_Name','Coord_RID','Coord_Email','TA_Code','TA_Contact_RID', \
                        'TA_Contact_Email','Student_Template','Non_Exempt_Template','Exempt_Template','Print_Leave')
        strColNames = ''
        for strColName in dictColNames:
            if len(strColNames) > 0:
                strColNames = strColNames  + ', ' + strColName
            else:
                strColNames = strColName
        strParams = ('Department_Code = ?', [strDeptCode])
        ctExistingRow = self._fSelect(strType, strColNames, strParams)
        i = 0
        bReturnVal = False
        strNewVal = ''
        strCurVal = ''
        for strColName in dictColNames:
            strNewVal = cNewRow[strColName]
            strCurVal = ctExistingRow[0][i]
            if len(strNewVal) > 0 and strCurVal != 'None':
                if strNewVal != strCurVal:
                    bReturnVal = True
                    break
            i += 1

        return bReturnVal


#****************************************************************************
#
#  Class: KIM update/insert Roles data
#
#****************************************************************************

class TKIMUtil(TSORUtil):
    _strName = 'KIM'
    _ctValidObjects = ['ROLES']
    
    def __init__(self, oLog, oProf):
        TSORUtil.__init__(self, self._strName, oLog, oProf)

        self._fConstructValidTables()


    #
    # Public interface
    #

    # Update the SOR_KIM_ROLES table
    #
    # Example XML:
    # <UpdateTable>
    #    <RolesTable>
    #       <RolesData>
    #          <Note>Manual xml update testing</Note>
    #          <RoleID>kimrole123</RoleID>
    #          <RoleName>purchaser</RoleName>
    #          <NameSpace>sr_kim</NameSpace>
    #          <Description>This role specifies that someone has the ability to make purchases from the KIM system</Description>
    #          <Active>Y</Active>
    #       </RolesData>
    #    </RolesTable>
    # </UpdateTable>
    def fUpdateRolesTable(self, oRoles, oDB):
        strType = "Roles"

        self._oDB = oDB

        strTbl = self._fGetTable(strType)
        if strTbl not in self._ctValidTables:
            strErr = "%s cannot update given table: %s" % \
                     (self._strName, strType)
            raise ERepository(125, strErr)

        #
        # parse xml to get key-value pairs
        #

        ctRoles = self._fParseRolesXML(oRoles)

        #
        # using parsed results, update table
        #

        ctRes = self._fUpdateRolesTable(strType, ctRoles)

        #
        # format response as portion of XML doc
        # (include RoleIDs processed)
        #

        strXMLRoleIDs = ''
        strXMLTempl = '<RoleID>%s</RoleID>'
        for sRoleID in ctRes:
            if strXMLRoleIDs:
                strXMLRoleIDs += '\n'
            strXMLRoleIDs += strXMLTempl % sRoleID

        return (strXMLRoleIDs, ctRes)
    
    #
    # Private interface
    #

    def _fParseRolesXML(self, oRoles):
        ctRolesRows = []

        for oRole in oRoles.childNodes:
            ctRoleRow = {}
            
            if oRole.nodeName == '#text':
                continue
            
            if oRole.hasChildNodes:
                for oRoleField in oRole.childNodes:
                    
                    if oRoleField.nodeName == '#text':
                        continue

                    if oRoleField.hasChildNodes:
                        if len(oRoleField.childNodes) > 0:
                            ctRoleRow[oRoleField.nodeName] = (oRoleField.childNodes[0].data).strip()
                        else:
                            ctRoleRow[oRoleField.nodeName] = ''
                            
                    else:
                        ctRoleRow[oRoleField.nodeName] = ''
                        
            ctRolesRows.append(ctRoleRow)

        return ctRolesRows

    def _fUpdateRolesTable(self, strType, ctRoles):
        """ Make sure to convert from unicode to ascii

        Database utility only handles ASCII...
        
        """
        ctSuccess = []
        for cRow in ctRoles:
            strRoleID = str(cRow['RoleID'])
            strCol = 'count(*)'
            strParams = ('RoleID = ?', [strRoleID])
            ctRes = self._fSelect(strType, strCol, strParams)
            if len(ctRes) == 0 or len(ctRes[0]) == 0 or int(ctRes[0][0]) == 0:
                # insert
                ctInsParams = ()
                ctCols = []
                ctVals = []
                ctBindVars = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    ctCols.append(sCol)
                    ctBindVars.append('?')
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                strBindVars = ','.join(ctBindVars)
                ctInsParams = (strCols, strBindVars, ctVals)
                self._fInsert(strType, ctInsParams)
                ctSuccess.append(strRoleID)
            elif int(ctRes[0][0]) == 1:
                # update
                ctUpdParams = ctSrchParams = ()
                ctCols = []
                ctVals = []
                for sCol, sVal in list(cRow.items()):
                    sCol = str(sCol)
                    sVal = str(sVal)
                    if sCol == 'RoleID':
                        continue
                    sCol = '%s = ?' % sCol
                    ctCols.append(sCol)
                    ctVals.append(sVal)
                strCols = ','.join(ctCols)
                ctUpdParams = (strCols, ctVals)
                ctSrchParams = ('RoleID = ?', [strRoleID])
                self._fUpdate(strType, ctUpdParams, ctSrchParams)
                ctSuccess.append(strRoleID)
            else:
                # error -- impossible because RoleID is primary key
                strErr = "Found multiple instances of same role (RoleID=%s)" % \
                         strRoleID
                raise ERepository(125, strErr)
        return ctSuccess

    def _fGetTable(self, strObj):
        strObj = strObj.upper()
        return '%s_%s_%s' % (TSORUtil._strName,
                             self._strName,
                             strObj)
        
    def _fConstructValidTables(self):
        for strObj in self._ctValidObjects:
            strTbl = '%s_%s_%s' % (TSORUtil._strName,
                                   self._strName,
                                   strObj)
            self._ctValidTables.append(strTbl)


#<<<<<<<<<<<<<<<<<<<<<<<<< MODS:JN:QUERY >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>
#****************************************************************************
#
#  Class encapsulating querying logic
#
#****************************************************************************

class TQuery(object):
    """ Handle SOR queries """

    sqlQuery_PK_USCID = """
       select distinct p.RID
       from PERSON p
       where p.Active_Flag = 'Y'
       and p.uscid = ?
       """

    sqlQuery_PK = """
       select distinct RID
       from PERSON
       where Active_Flag = 'Y'
       and RID = ?
       """

    sqlQuery_PK_SSN = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       """

    sqlQuery_PK_SSNL4 = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       """

    sqlQuery_SSN = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pi.SSN_Value = ?
       """

    sqlQuery_SSNL4 = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pi.SSN_Value like ?
       """

    sqlQuery_PK_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pn.RID = p.RID
       and p.RID = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pn.RID = p.RID
       and p.RID = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pn.RID = p.RID
       and p.RID = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pn.RID = p.RID
       and p.RID = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pn.RID = p.RID
       and p.RID = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_BirthDate = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and p.RID = ?
       and pd.BIRTHDATE_Value = ?
       """

    sqlQuery_PK_SSN_BirthDate = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       """

    sqlQuery_PK_SSNL4_BirthDate = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       """

    sqlQuery_SSN_BirthDate = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       """

    sqlQuery_SSNL4_BirthDate = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       """

    sqlQuery_PK_BirthDate_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_BirthDate_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_BirthDate_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_BirthDate_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_BirthDate_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_BirthDate_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_BirthDate_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_BirthDate_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_BirthDate_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_BirthDate_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_BirthDate_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_BirthDate_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_BirthDate_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_BirthDate_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_BirthDate_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSN_BirthDate_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_BirthDate_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_BirthDate_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_SSNL4_BirthDate_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_BirthDate_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_BirthDate_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSN_BirthDate_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value = ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_BirthDate_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_BirthDate_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_PK_SSNL4_BirthDate_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_IDS pi, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pd.RID = p.RID
       and pn.RID = p.RID
       and p.RID = ?
       and pi.SSN_Value like ?
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """

    sqlQuery_BirthDate_LastExact = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """
    
    sqlQuery_BirthDate_LastFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """
    
    sqlQuery_BirthDate_LastExact_FirstExact = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and pn.First_STRP_Value = ?
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """
    
    sqlQuery_BirthDate_LastExact_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and pn.Last_STRP_Value = ?
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """
    
    sqlQuery_BirthDate_LastFuzzy_FirstFuzzy = """
       select distinct p.RID
       from PERSON p, PERSON_DEMO pd, PERSON_Name pn
       where p.Active_Flag = 'Y'
       and pd.RID = p.RID
       and pn.RID = p.RID
       and pd.BIRTHDATE_Value = ?
       and soundex(pn.Last_STRP_Value) = soundex(?)
       and soundex(pn.First_STRP_Value) = soundex(?)
       and pn.GTYPE_ID in (select GTYPE_ID from META_GROUP_TYPE where GROUP_ID = ? and GTYPE_NAME in (%s))
       """
    
    sqlGetActiveUSCID = """
       select distinct p.RID
       from PERSON p, PERSON_IDs pi
       where p.Active_Flag = 'Y'
       and pi.RID = p.RID
       and pi.%s_Value = ?
       """

    def __init__(self, oLog, oProf):
        self._oLog = oLog
        self._oProf = oProf
        
        self.ctQueryFilter = {}
        self.ctQueryFilter['SIS'] = {}
        self.ctQueryFilter['iVIP'] = {}

        self.ctQueryFilter['SIS'][('PKs', None)] = ['USCID']
        self.ctQueryFilter['SIS'][('IDs', None)] = ['SSN', 'SISPID', 'EmployeeID', 'iVIPID']
        self.ctQueryFilter['SIS'][('Demo', None)] = ['BirthDate']
        self.ctQueryFilter['SIS'][('Name', 'Verified')] = ['First', 'Last', 'Middle', 'Salutation', 'Suffix']
        self.ctQueryFilter['SIS'][('Name', 'Reported')] = ['First', 'Last', 'Middle', 'Salutation', 'Suffix']
        self.ctQueryFilter['SIS'][('Name', 'VIP')] = ['First', 'Last', 'Middle', 'Salutation', 'Suffix']
        self.ctQueryFilter['SIS'][('Address', 'Local')] = ['Line1', 'Line2', 'City', 'State', 'Zip', 'Province', 'Country', 'Phone']
        self.ctQueryFilter['SIS'][('Address', 'Permanent')] = ['Line1', 'Line2', 'City', 'State', 'Zip', 'Province', 'Country', 'Phone']
        self.ctQueryFilter['SIS'][('Address', 'Foreign')] = ['Line1', 'Line2', 'City', 'State', 'Zip', 'Province', 'Country', 'Phone']
        self.ctQueryFilter['SIS'][('Address', 'Home')] = ['Line1', 'Line2', 'City', 'State', 'Zip', 'Province', 'Country', 'Phone']
        self.ctQueryFilter['SIS'][('EmployeeInfo', None)] = ['WorkPhone', 'WorkCell', 'PreferredEmail']
        self.ctQueryFilter['SIS'][('USCOffice', 'Work')] = ['BuildingCode', 'CampusCode', 'Line1', 'Line2', 'Municipality', 'Region', 'ZipCode']

        self.ctQueryFilter['iVIP'][('PKs', None)] = ['USCID']
        self.ctQueryFilter['iVIP'][('Privacy', None)] = ['StudentConfidentiality', 'StudentReleaseDir',
                                                         'EmpReleaseDir', 'EmpReleaseHomeAddress', 'EmpReleaseHomePhone']
        self.ctQueryFilter['iVIP'][('Name', 'Verified')] = ['First', 'Last', 'Middle']
        self.ctQueryFilter['iVIP'][('Name', 'Reported')] = ['First', 'Last', 'Middle']
        self.ctQueryFilter['iVIP'][('Name', 'VIP')] = ['First', 'Last']
        self.ctQueryFilter['iVIP'][('Address', 'Local')] = ['Line1', 'Line2', 'City', 'State', 'Zip', 'Zip4', 'Country', 'Phone']
        self.ctQueryFilter['iVIP'][('Address', 'Permanent')] = ['Line1', 'Line2', 'City', 'State', 'Zip', 'Zip4', 'Country', 'Phone']
        self.ctQueryFilter['iVIP'][('Address', 'Home')] = ['Line1', 'City', 'State', 'Zip', 'Phone']
        self.ctQueryFilter['iVIP'][('EmployeeInfo', None)] = ['WorkPhone', 'WorkCell', 'PreferredEmail']

    def fGetQueryFilter(self):
        return copy.deepcopy(self.ctQueryFilter)

    def fGetActiveUSCID(self, oP, ctMatches, strSOR, oDB, ctSORPKs, **kw):
        # if we matched by PK, nothing further to do..
        if len(ctMatches) != 0:
            return ctMatches

        #
        # For now restrict this to certain SORs
        #
        ctAllowedSORs = ['ADMIN', 'iVIP', 'GDS']
        if strSOR not in ctAllowedSORs:
            return ctMatches

        #
        # Some SORs may need to search using another SOR's ID
        # attribute, e.g. GDS can supply iVIPID and get USCID back.
        #
        ctAllowedIDs = dict(ADMIN=['iVIPID'],
                            GDS=['iVIPID'])

        self._oDB = oDB
        self._ctSORPKs = ctSORPKs

        ctQueryMatches = []
        bFoundID = False
        
        strID = self._ctSORPKs.get(strSOR)
        ctAG_IDS = oP.ctAttrGroups.get(('IDs',), None)
        if ctAG_IDS is not None:
            oID = ctAG_IDS[0].ctAttrs.get((strID,))
            if oID and len(oID.strValue) > 0:
                bFoundID = True
            # check for exceptions...
            if strSOR in ctAllowedIDs:
                for strID in ctAllowedIDs[strSOR]:
                    oID = ctAG_IDS[0].ctAttrs.get((strID,))
                    if oID and len(oID.strValue) > 0:
                        bFoundID = True
                        break
                
        if not bFoundID:
            raise ERepository(129, "SOR did not provide information required for USCID request")

        sqlSelect = self.sqlGetActiveUSCID % (strID)
        ctRes = self._oDB.fSelect(sqlSelect, [oID.strDBValue])

        # if nothing returned, bad IDs:
        if len(ctRes) == 0:
            raise ERepository(110, "Invalid %s: %s" % (strID, oID.strValue))
        
        for ctRID_ in ctRes:
            iRID_ = ctRID_[0]
            if iRID_ not in ctQueryMatches:
                ctQueryMatches.append(iRID_)
                                                            
        return ctQueryMatches

    def fGetMatches(self, oP, ctMatches, strSOR, oDB, **kw):
        self._oDB = oDB

        strCall = 'self._fPerform%sQuery' % strSOR
        return eval(strCall)(oP, ctMatches, **kw)

    # This method was previously used by SIS queries before
    # the set of iVIP methods were copied and modified for
    # use by SIS.  The code in this method now resides in
    # the method: _fPerformSISQueryDefault
    def _fPerformDefaultQuery(self, oP, ctMatches, **kw):
        """
        Required:
          USCID
          Last Name (type Verified or Reported)
        
        """
        
        ctQueryMatches = []
        
        if len(ctMatches) == 0:
            return ctQueryMatches
                    
        #
        # Since we have matched by PK, we can assume
        # that we're already dealing with active records
        #

        bFoundLast = False
        
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'Verified'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'Reported'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R

        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        if not bFoundLast:
            raise ERepository(130, "SOR did not provide information required for person query")

        # name types to query for matches
        ctNameTypes = []
        ctNameTypes.append("'Reported'")
        ctNameTypes.append("'Verified'")
            
        for iRID in ctMatches:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    sqlSelect = self.sqlQuery_PK_LastExact % ','.join(ctNameTypes)
                    ctRes = self._oDB.fSelect(sqlSelect, [\
                                              iRID,
                                              oLast.strDBValue,
                                              oAGName.oMGroup.iGroupID])
                    self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)

        return ctQueryMatches

    def _fPerformSISQuery(self, oP, ctMatches, **kw):
        bMatchExact = kw.get('bMatchExact')
        bMatchPartial = kw.get('bMatchPartial')

        strQueryType = 'Default'
        
        if bMatchExact and bMatchPartial:
            strQueryType = 'Comprehensive'
        elif bMatchExact:
            strQueryType = 'Exact'
        elif bMatchPartial:
            strQueryType = 'Partial'

        self._oLog.fDebug('SIS Query Type: ' + strQueryType)
        strCall = 'self._fPerformSISQuery%s' % strQueryType
        return eval(strCall)(oP, ctMatches, **kw)
            
    def _fPerformSISQueryDefault(self, oP, ctMatches, **kw):
        """
        Required:
          USCID
        Optional:
          Last Name (type Verified or Reported)
        
        """
        
        ctQueryMatches = []
        
        if len(ctMatches) == 0:
            raise ERepository(130, "SOR did not provide information required for person query")

        #
        # Since we have matched by PK, we can assume
        # that we're already dealing with active records
        #

        bFoundLast = False
        
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'Verified'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'Reported'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R

        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        # name types to query for matches
        ctNameTypes = []
        ctNameTypes.append("'Reported'")
        ctNameTypes.append("'Verified'")
        ctNameTypes.append("'VIP'")
        ctNameTypes.append("'VIPDisplay'")
            
        for iRID in ctMatches:
            if bFoundLast:
                for oAGName in ctAG_Name:
                    oLast = oAGName.ctAttrs.get(('Last_STRP',))
                    if (oLast) and len(oLast.strValue) > 0:
                        # PK, Last
                        sqlSelect = self.sqlQuery_PK_LastExact % ','.join(ctNameTypes)
                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                  iRID,
                                                  oLast.strDBValue,
                                                  oAGName.oMGroup.iGroupID])
                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
            else:
                sqlSelect = self.sqlQuery_PK
                ctRes = self._oDB.fSelect(sqlSelect, [iRID])
                self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)

        return ctQueryMatches

    def _fPerformSISQueryComprehensive(self, oP, ctMatches, **kw):
        ctQueryMatches = self._fPerformSISQueryExact(oP, ctMatches, **kw)
        return self._fPerformSISQueryPartial(oP, ctQueryMatches, **kw)

    def _fPerformSISQueryExact(self, oP, ctMatches, **kw):
        """
        Required at least two of the following:
          USCID
          SSN
          BirthDate
          Last Name (type Verified or Reported)
        Optional:
          First Name (type Verified or Reported)
        
        """

        ctQueryMatches = []

        bFoundPK = False
        bFoundSSN = False
        bFoundSSNL4 = False
        bFoundDOB = False
        bFoundLast = False
        
        ctAG_IDs = oP.ctAttrGroups.get(('IDs',), None)
        ctAG_DEMO = oP.ctAttrGroups.get(('Demo',), None)
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'Verified'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'Reported'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R

        if len(ctMatches) > 0:
            bFoundPK = True

        if ctAG_IDs is not None:
            oSSN = ctAG_IDs[0].ctAttrs.get(('SSN',))
            if oSSN and len(oSSN.strValue) > 0:
                bFoundSSN = True

        if ctAG_IDs is not None:
            oSSNL4 = ctAG_IDs[0].ctAttrs.get(('SSNLast4Digits',))
            if oSSNL4 and len(oSSNL4.strValue) > 0:
                ssnl4 = '%' + oSSNL4.strDBValue
                bFoundSSNL4 = True

        if ctAG_DEMO is not None:
            oBD = ctAG_DEMO[0].ctAttrs.get(('BirthDate',))
            if oBD and len(oBD.strValue) > 0:
                bFoundDOB = True
                
        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        # name types to query for matches
        ctNameTypes = []
        ctNameTypes.append("'Reported'")
        ctNameTypes.append("'Verified'")
        ctNameTypes.append("'VIP'")
        ctNameTypes.append("'VIPDisplay'")
            
        if bFoundPK:
            for iRID in ctMatches:
                if bFoundSSN:
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSN, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSN_BirthDate_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSN, BirthDate, Last
                                        sqlSelect = self.sqlQuery_PK_SSN_BirthDate_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSN, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSN_BirthDate, [\
                                                      iRID,
                                                      oSSN.strDBValue,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSN, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSN_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSN, Last
                                        sqlSelect = self.sqlQuery_PK_SSN_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSN
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSN, [\
                                                      iRID,
                                                      oSSN.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                elif bFoundSSNL4:
                    # self._oLog.fDebug('SSN Lenght: ' + str(len(oSSNL4.strDBValue)));
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSNL4, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSNL4_BirthDate_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSNL4, BirthDate, Last
                                        sqlSelect = self.sqlQuery_PK_SSNL4_BirthDate_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSNL4, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSNL4_BirthDate, [\
                                                      iRID,
                                                      ssnl4,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSNL4, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSNL4_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSNL4, Last
                                        sqlSelect = self.sqlQuery_PK_SSNL4_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSNL4
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSNL4, [iRID, ssnl4])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)                    
                else: # No SSN
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_PK_BirthDate_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, BirthDate, Last
                                        sqlSelect = self.sqlQuery_PK_BirthDate_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_BirthDate, [\
                                                      iRID,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, Last, First
                                        sqlSelect = self.sqlQuery_PK_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, Last
                                        sqlSelect = self.sqlQuery_PK_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK, [iRID])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
        else: # No PK
                if bFoundSSN:
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSN, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_SSN_BirthDate_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSN, BirthDate, Last
                                        sqlSelect = self.sqlQuery_SSN_BirthDate_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSN, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_SSN_BirthDate, [\
                                                      oSSN.strDBValue,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSN, Last, First
                                        sqlSelect = self.sqlQuery_SSN_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSN, Last
                                        sqlSelect = self.sqlQuery_SSN_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSN
                            ctRes = self._oDB.fSelect(self.sqlQuery_SSN, [oSSN.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                elif bFoundSSNL4:
                    # self._oLog.fDebug('SSN Lenght: ' + str(len(oSSNL4.strDBValue)));
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSNL4, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_SSNL4_BirthDate_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSNL4, BirthDate, Last
                                        sqlSelect = self.sqlQuery_SSNL4_BirthDate_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSNL4, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_SSNL4_BirthDate, [\
                                                      ssnl4,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSNL4, Last, First
                                        sqlSelect = self.sqlQuery_SSNL4_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSNL4, Last
                                        sqlSelect = self.sqlQuery_SSNL4_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSNL4
                            raise ERepository(130, "SOR did not provide information required for person query")
                            # ctRes = self._oDB.fSelect(self.sqlQuery_SSNL4, [ssnl4])
                            # self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    
                else: # No SSN
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_BirthDate_LastExact_FirstExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # BirthDate, Last
                                        sqlSelect = self.sqlQuery_BirthDate_LastExact % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # BirthDate
                            raise ERepository(130, "SOR did not provide information required for person query")
                    else: # No DOB
                        # Last if bFoundLast is true - Not enough information
                        raise ERepository(130, "SOR did not provide information required for person query")

        return ctQueryMatches

    def _fPerformSISQueryPartial(self, oP, ctMatches, **kw):
        """
        Required at least two of the following:
          USCID
          SSN
          BirthDate
          Last Name (type Verified or Reported)
        Optional:
          First Name (type Verified or Reported)
        
        """

        ctQueryMatches = []

        bFoundPK = False
        bFoundSSN = False
        bFoundSSNL4 = False
        bFoundDOB = False
        bFoundLast = False
        
        ctAG_IDs = oP.ctAttrGroups.get(('IDs',), None)
        ctAG_DEMO = oP.ctAttrGroups.get(('Demo',), None)
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'Verified'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'Reported'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R

        if len(ctMatches) > 0:
            bFoundPK = True

        if ctAG_IDs is not None:
            oSSN = ctAG_IDs[0].ctAttrs.get(('SSN',))
            if oSSN and len(oSSN.strValue) > 0:
                bFoundSSN = True

        if ctAG_IDs is not None:
            oSSNL4 = ctAG_IDs[0].ctAttrs.get(('SSNLast4Digits',))
            if oSSNL4 and len(oSSNL4.strValue) > 0:
                ssnl4 = '%' + oSSNL4.strDBValue
                bFoundSSNL4 = True

        if ctAG_DEMO is not None:
            oBD = ctAG_DEMO[0].ctAttrs.get(('BirthDate',))
            if oBD and len(oBD.strValue) > 0:
                bFoundDOB = True
                
        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        # name types to query for matches
        ctNameTypes = []
        ctNameTypes.append("'Reported'")
        ctNameTypes.append("'Verified'")
        ctNameTypes.append("'VIP'")
        ctNameTypes.append("'VIPDisplay'")
            
        if bFoundPK:
            for iRID in ctMatches:
                if bFoundSSN:
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSN, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSN_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSN, BirthDate, Last
                                        sqlSelect = self.sqlQuery_PK_SSN_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSN, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSN_BirthDate, [\
                                                      iRID,
                                                      oSSN.strDBValue,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSN, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSN_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSN, Last
                                        sqlSelect = self.sqlQuery_PK_SSN_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSN
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSN, [\
                                                      iRID,
                                                      oSSN.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                elif bFoundSSNL4:
                    # self._oLog.fDebug('SSN Lenght: ' + str(len(oSSNL4.strDBValue)));
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSNL4, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSNL4_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSNL4, BirthDate, Last
                                        sqlSelect = self.sqlQuery_PK_SSNL4_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSNL4, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSNL4_BirthDate, [\
                                                      iRID,
                                                      ssnl4,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, SSNL4, Last, First
                                        sqlSelect = self.sqlQuery_PK_SSNL4_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, SSNL4, Last
                                        sqlSelect = self.sqlQuery_PK_SSNL4_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, SSNL4
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_SSNL4, [iRID, ssnl4])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                else: # No SSN
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_PK_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, BirthDate, Last
                                        sqlSelect = self.sqlQuery_PK_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK_BirthDate, [\
                                                      iRID,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # PK, Last, First
                                        sqlSelect = self.sqlQuery_PK_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                    else: # No First
                                        # PK, Last
                                        sqlSelect = self.sqlQuery_PK_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  iRID,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                        else: # No Last
                            # PK
                            ctRes = self._oDB.fSelect(self.sqlQuery_PK, [iRID])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
        else: # No PK
                if bFoundSSN:
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSN, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_SSN_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSN, BirthDate, Last
                                        sqlSelect = self.sqlQuery_SSN_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSN, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_SSN_BirthDate, [\
                                                      oSSN.strDBValue,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSN, Last, First
                                        sqlSelect = self.sqlQuery_SSN_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSN, Last
                                        sqlSelect = self.sqlQuery_SSN_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oSSN.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSN
                            ctRes = self._oDB.fSelect(self.sqlQuery_SSN, [oSSN.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                elif bFoundSSNL4:
                    # self._oLog.fDebug('SSN Lenght: ' + str(len(oSSNL4.strDBValue)));
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSNL4, BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_SSNL4_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSNL4, BirthDate, Last
                                        sqlSelect = self.sqlQuery_SSNL4_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSNL4, BirthDate
                            ctRes = self._oDB.fSelect(self.sqlQuery_SSNL4_BirthDate, [\
                                                      ssnl4,
                                                      oBD.strDBValue])
                            self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                    else: # No DOB
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                ctRes = []
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # SSNL4, Last, First
                                        sqlSelect = self.sqlQuery_SSNL4_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # SSNL4, Last
                                        sqlSelect = self.sqlQuery_SSNL4_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  ssnl4,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # SSNL4
                            raise ERepository(130, "SOR did not provide information required for person query")
                            # ctRes = self._oDB.fSelect(self.sqlQuery_SSNL4, [ssnl4])
                            # self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    
                else: # No SSN
                    if bFoundDOB:
                        if bFoundLast:
                            for oAGName in ctAG_Name:
                                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                                if (oLast) and len(oLast.strValue) > 0:
                                    # first name only makes sense in context of last name..
                                    if (oFirst) and len(oFirst.strValue) > 0:
                                        # BirthDate, Last, First
                                        sqlSelect = self.sqlQuery_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oFirst.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                                    else: # No First
                                        # BirthDate, Last
                                        sqlSelect = self.sqlQuery_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                                  oBD.strDBValue,
                                                                  oLast.strDBValue,
                                                                  oAGName.oMGroup.iGroupID])
                                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                        else: # No Last
                            # BirthDate
                            raise ERepository(130, "SOR did not provide information required for person query")
                    else: # No DOB
                        # Last if bFoundLast is true - Not enough information
                        raise ERepository(130, "SOR did not provide information required for person query")

        return ctQueryMatches
    
    def _fPerformiVIPQuery(self, oP, ctMatches, **kw):
        bMatchExact = kw.get('bMatchExact')
        bMatchPartial = kw.get('bMatchPartial')

        strQueryType = 'Default'
        
        if bMatchExact and bMatchPartial:
            strQueryType = 'Comprehensive'
        elif bMatchExact:
            strQueryType = 'Exact'
        elif bMatchPartial:
            strQueryType = 'Partial'

        strCall = 'self._fPerformiVIPQuery%s' % strQueryType
        return eval(strCall)(oP, ctMatches, **kw)
            
    def _fPerformiVIPQueryDefault(self, oP, ctMatches, **kw):
        ctQueryMatches = []
        
        bFoundDOB = False
        bFoundLast = False
        
        ctAG_DEMO = oP.ctAttrGroups.get(('Demo',), None)
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'VIP'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'VIPDisplay'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R
        
        if ctAG_DEMO is not None:
            oBD = ctAG_DEMO[0].ctAttrs.get(('BirthDate',))
            if oBD and len(oBD.strValue) > 0:
                bFoundDOB = True
                
        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        # name types to query for matches
        ctNameTypes = []
        ctNameTypes.append("'Reported'")
        ctNameTypes.append("'Verified'")
        ctNameTypes.append("'VIP'")
        ctNameTypes.append("'VIPDisplay'")
            
        if len(ctMatches) > 0:
            #
            # Since we have matched by PK, we can assume
            # that we're already dealing with active records
            #

            if not bFoundDOB and not bFoundLast:
                raise ERepository(130, "SOR did not provide information required for person query")
            
            # matching by PK, expect one match per RID..
            for iRID in ctMatches:
                if bFoundDOB:
                    if bFoundLast:
                        for oAGName in ctAG_Name:
                            oLast = oAGName.ctAttrs.get(('Last_STRP',))
                            oFirst = oAGName.ctAttrs.get(('First_STRP',))
                            if (oLast) and len(oLast.strValue) > 0:
                                # first name only makes sense in context of last name..
                                if (oFirst) and len(oFirst.strValue) > 0:
                                    # PK, BirthDate, Last, First
                                    sqlSelect = self.sqlQuery_PK_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                    ctRes = self._oDB.fSelect(sqlSelect, [\
                                                              iRID,
                                                              oBD.strDBValue,
                                                              oLast.strDBValue,
                                                              oFirst.strDBValue,
                                                              oAGName.oMGroup.iGroupID])
                                    self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                                else:
                                    # PK, BirthDate, Last
                                    sqlSelect = self.sqlQuery_PK_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                                    ctRes = self._oDB.fSelect(sqlSelect, [\
                                                              iRID,
                                                              oBD.strDBValue,
                                                              oLast.strDBValue,
                                                              oAGName.oMGroup.iGroupID])
                                    self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                    else:
                        # PK, BirthDate
                        ctRes = self._oDB.fSelect(self.sqlQuery_PK_BirthDate, [\
                                                  iRID,
                                                  oBD.strDBValue])
                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                else:
                    # given PK, Last
                    for oAGName in ctAG_Name:
                        ctRes = []
                        oLast = oAGName.ctAttrs.get(('Last_STRP',))
                        oFirst = oAGName.ctAttrs.get(('First_STRP',))
                        if (oLast) and len(oLast.strValue) > 0:
                            # first name only makes sense in context of last name..
                            if (oFirst) and len(oFirst.strValue) > 0:
                                # PK, Last, First
                                sqlSelect = self.sqlQuery_PK_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                                ctRes = self._oDB.fSelect(sqlSelect, [\
                                                          iRID,
                                                          oLast.strDBValue,
                                                          oFirst.strDBValue,
                                                          oAGName.oMGroup.iGroupID])
                                self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)
                            else:
                                # PK, Last
                                sqlSelect = self.sqlQuery_PK_LastFuzzy % ','.join(ctNameTypes)
                                ctRes = self._oDB.fSelect(sqlSelect, [\
                                                          iRID,
                                                          oLast.strDBValue,
                                                          oAGName.oMGroup.iGroupID])
                                self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)

        else: # no PK
            #
            # We'll only lookup active records
            #
            
            if not bFoundDOB or not bFoundLast:
                raise ERepository(130, "SOR did not provide information required for person query")
            
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    # first name only makes sense in context of last name..
                    if (oFirst) and len(oFirst.strValue) > 0:
                        # BirthDate, Last, First
                        sqlSelect = self.sqlQuery_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                  oBD.strDBValue,
                                                  oLast.strDBValue,
                                                  oFirst.strDBValue,
                                                  oAGName.oMGroup.iGroupID])
                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)
                    else:
                        # BirthDate, Last
                        sqlSelect = self.sqlQuery_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                  oBD.strDBValue,
                                                  oLast.strDBValue,
                                                  oAGName.oMGroup.iGroupID])
                        self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=0)

        return ctQueryMatches

    def _fPerformiVIPQueryComprehensive(self, oP, ctMatches, **kw):
        ctQueryMatches = self._fPerformiVIPQueryExact(oP, ctMatches, **kw)
        return self._fPerformiVIPQueryPartial(oP, ctQueryMatches, **kw)

    def _fPerformiVIPQueryExact(self, oP, ctMatches, **kw):
        """ Expect:

        USCID
        Last (required), First (optional)
        DOB
        
        """

        ctQueryMatches = []
        
        bFoundDOB = False
        bFoundLast = False
        
        ctAG_DEMO = oP.ctAttrGroups.get(('Demo',), None)
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'VIP'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'VIPDisplay'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R
        
        if ctAG_DEMO is not None:
            oBD = ctAG_DEMO[0].ctAttrs.get(('BirthDate',))
            if oBD and len(oBD.strValue) > 0:
                bFoundDOB = True
                
        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        if len(ctMatches) == 0 \
               or not bFoundDOB \
               or not bFoundLast:
            raise ERepository(130, "SOR did not provide information required for person query using exact match")
            
        # name types to query for matches
        ctNameTypes = []
        ctNameTypes.append("'Reported'")
        ctNameTypes.append("'Verified'")
        ctNameTypes.append("'VIP'")
        ctNameTypes.append("'VIPDisplay'")

        for iRID in ctMatches:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                oFirst = oAGName.ctAttrs.get(('First_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    # first name only makes sense in context of last name..
                    if (oFirst) and len(oFirst.strValue) > 0:
                        # PK, BirthDate, Last, First
                        sqlSelect = self.sqlQuery_PK_BirthDate_LastFuzzy_FirstFuzzy % ','.join(ctNameTypes)
                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                  iRID,
                                                  oBD.strDBValue,
                                                  oLast.strDBValue,
                                                  oFirst.strDBValue,
                                                  oAGName.oMGroup.iGroupID])
                    else:
                        # PK, BirthDate, Last
                        sqlSelect = self.sqlQuery_PK_BirthDate_LastFuzzy % ','.join(ctNameTypes)
                        ctRes = self._oDB.fSelect(sqlSelect, [\
                                                  iRID,
                                                  oBD.strDBValue,
                                                  oLast.strDBValue,
                                                  oAGName.oMGroup.iGroupID])
                    self._fProcessMatches(ctRes, ctQueryMatches, bOneMatch=1)

        return ctQueryMatches

    def _fPerformiVIPQueryPartial(self, oP, ctMatches, **kw):
        """ Expect:

        USCID
        Last (required), First (optional)
        DOB

        Matching done on following combos:
          USCID + Last + First (optional)
          USCID + DOB
          DOB + Last + First (optional)
          
        """

        bNotImplemented = True
        if bNotImplemented:
            raise ERepository(213, "Partial match query not yet implemented!")
        
        ctQueryMatches = []
        
        bFoundDOB = False
        bFoundLast = False
        
        ctAG_DEMO = oP.ctAttrGroups.get(('Demo',), None)
        ctAG_Name_V = oP.ctAttrGroups.get(('Name', 'VIP'), [])
        ctAG_Name_R = oP.ctAttrGroups.get(('Name', 'VIPDisplay'), [])
        ctAG_Name = ctAG_Name_V + ctAG_Name_R
        
        if ctAG_DEMO is not None:
            oBD = ctAG_DEMO[0].ctAttrs.get(('BirthDate',))
            if oBD and len(oBD.strValue) > 0:
                bFoundDOB = True
                
        if len(ctAG_Name) > 0:
            for oAGName in ctAG_Name:
                oLast = oAGName.ctAttrs.get(('Last_STRP',))
                if (oLast) and len(oLast.strValue) > 0:
                    bFoundLast = True

        return ctQueryMatches


    def _fProcessMatches(self, ctRes, ctQueryMatches, bOneMatch=0):
        if bOneMatch:
            if len(ctRes) > 1:
                raise ERepository(122, 'Query matched multiple records: %d matches' % (len(ctRes)))
            if len(ctRes) > 0:
                iRID_ = ctRes[0][0]
                if iRID_ not in ctQueryMatches:
                    ctQueryMatches.append(iRID_)
        else:
            # multiple matches possible
            if len(ctRes) > 0:
                for ctRID_ in ctRes:
                    iRID_ = ctRID_[0]
                    if iRID_ not in ctQueryMatches:
                        ctQueryMatches.append(iRID_)



#
# -=EOF=-
#
