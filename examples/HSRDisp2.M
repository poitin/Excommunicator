DEFINITIONS

GetPrescription {} = 
(user(uid).requestPrescription<uid,pid1>.prescriptionDB(did,docid).
dispense<uid,did,docid>.0 ) . GetPrescription {}

PrescriptionDB {} = new uid. ( new pid .(
requestPrescription(uid,pid).
(prescriptionDB<did1,doctor1>.0 + prescriptionDB<did2,doctor2>.0). PrescriptionDB {}))

DispensationService {} = dispense (userID, prescriptionID, doctorID).0


ENDD


SYSTEM

(user<doctor1>.0 + user<nurse1>.0) | GetPrescription {} | PrescriptionDB {} | DispensationService {}


ENDS


PROPERTIES

G (not (uid = docid))

ENDP

