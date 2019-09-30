DEFINITIONS

P {a,b,c,f,g} = a[1.0,2.5]<b,f>.a[2.0,4.0]<c,g>.0
Q {d,e,h} = d(e,h).d(e,h).[x=e]0

ENDD


SYSTEM

P{y,x,w,u,v} | Q {y,z,r}

ENDS

PROPERTIES

y(*,*) before [10.0+2.0, 25.0 - 5.0]

y(*,u) before [35.0 mod 25.0, 75.0 mod 50.0]

y(*,*) before [0.8, 1.0]

ENDP
