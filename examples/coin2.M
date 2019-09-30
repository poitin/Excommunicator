DEFINITIONS

tosser{} = ((toss<head>.0) +[0.5] (toss<tail>.0)) | (toss(result).0)

ENDD

SYSTEM

tosser{} + tosser{}

ENDS

PROPERTIES

(F(result=head))@1.0
F(result=head)

ENDP

