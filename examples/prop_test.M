DEFINITIONS

P {a,b,c,f,g} = a[1.0,2.5]<b,f>.a[2.0,4.0]<c,g>.0
Q {d,e,h} = d(e,h).d(e,h).[x=e]0

ENDD


SYSTEM

P{y,x,w,u,v} | Q {y,z,r}

ENDS

PROPERTIES

F(e=x)

y(w,v) > y (x, u)

y(w,*) > y (x, *)

y(*,*) > y (*,*)

y(x,u) > y (w ,v)

F(e=x and not e=w)

ENDP
