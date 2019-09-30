DEFINITIONS

GetPrescription {} = 
(user(uid).requestPrescription<uid,pid>.prescriptionDB(pstatus,did,docid).
dispense<uid,did,docid>.0 ) . GetPrescription {}

PrescriptionDB {} = new uid. ( new pid .(
requestPrescription(uid,pid).
(prescriptionDB<valid,did1,doctor1>.0 + prescriptionDB<valid,did2,doctor2>.0). PrescriptionDB {}))

DispensationService {} = dispense (userID, prescriptionID, doctorID).0


ENDD


SYSTEM

user<doctor1>.0 + user<nurse1>.0 | GetPrescription {} | PrescriptionDB {} | DispensationService {} | (exit().0)


ENDS


PROPERTIES

G((dispense (uid, did, docid)> prescriptionDB (pstatus, did, docid)) and not (uid = docid))
G(dispense (uid, did, docid)> prescriptionDB (pstatus, did, docid))
dispense (uid, did, docid)> prescriptionDB (pstatus, did, docid)
dispense (nurse1, did1, doctor1)> prescriptionDB (valid, did1, doctor1)
G(dispense (nurse1, did1, doctor1)> prescriptionDB (valid, did1, doctor1))
G(not(uid=docid))

ENDP

