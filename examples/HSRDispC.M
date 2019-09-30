DEFINITIONS

GetPrescription {} = 
user(uid).requestPrescription<uid,pid>.prescriptionDB(pstatus,did,docid).
dispense<uid,did,docid>. check<uid, docid>. GetPrescription {}

PrescriptionDB {} = new uid. ( new pid .(
requestPrescription(uid,pid).
(prescriptionDB<valid,did1,doctor1>.0 + prescriptionDB<valid,did2,doctor2>.0). PrescriptionDB {}))

DispensationService {} = dispense (userID, prescriptionID, doctorID).0

CheckSoD {} = check (uid,docid). if (docid = uid) then SoDEvent <uid>.0 else noSoD< >.0 fi . CheckSoD {}

JustificationEnabled {} = setJustification(level). SoDEvent (uid). 
if (level = disable) then noJustification < >.0 else requireJustification<uid>.0 fi . JustificationEnabled {}

WaitForJustification {} = requireJustification(uid).setTimer<t24h>.((justification(uid1).
if (uid1=uid) then justificationOK<uid>.0 else escalate< >.0 fi .0) + alarm ( ). escalate < >. 0) .
WaitForJustification {}

TimerService {} = setTimer(period). alarm[23.9,24.0]< >. TimerService {}


ENDD


SYSTEM

(user<doctor1>.0 + user<nurse1>.0) | GetPrescription {} | PrescriptionDB {} | DispensationService {} | CheckSoD {} |
JustificationEnabled {} | WaitForJustification {} | TimerService {} | noSoD().0 | noJustification().0 | escalate ().0 |
justificationOK(tuid).0 | setJustification<enable>.0 | (justification[0.0,25.0]<doctor1>.0 + justification[0.0,25.0]<doctor2>.0).0


ENDS


PROPERTIES

G (dispense (uid, did) > prescriptionDB (pstatus, did, docid))
G (escalate( ) > requireJustification(uid))
G (justificationOK (uid) within [requireJustification(uid), requireJustification(uid)+24.0])
G (escalate( ) within [requireJustification(uid), requireJustification(uid)+24.0])

ENDP

