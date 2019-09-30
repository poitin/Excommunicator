DEFINITIONS

P {a,b,c,f,g} = a[1.0,2.5]<b,f>.a[2.0,4.0]<c,g>.0
Q {d,e,h} = d(e,h).d(e,h).[x=e]0

ENDD


SYSTEM

P{y,x,w,u,v} | Q {y,z,r}

ENDS

PROPERTIES

G ( not (y(v,*)) )
F ( y(w,*) )

G( G(not(y(v,*))))
F ( F (y(w,*)) )

F ( G (not (y(v,*)) ) )
G(F((y(w,*))))

F( F ( G ( not (y(v,*)) ) ) )
G(G(F(y(w,*))))

G(F(G(not(y(v,*)))))
F(G(F(y(w,*))))

ENDP
