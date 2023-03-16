# Excommunicator
Transformation Tool to Remove Internal Communication from Pi-Calculus Processes using the
Blazed Excommunication Algorithm as described in the paper "Excommunication: Transforming Pi-Calculus Specifications to Remove Internal Communication"

The implementation can be built and executed using stack.

## Execution 
The execution is a REPL, with the prompt "Pi> " and the following commands:

```
Pi> :help

:load filename	To load a file
:proc		    To show the current process
:spec		    To show the current specification
:transform	    To transform the current process
:help		    To print this message
:quit		    To quit
```
The first thing to do is to load a specification file:

```
Pi> :load doublebuffer
```

This will load the specification doublebuffer.pi (the.pi extension is assumed).

To see the contents of this specification:

```
Pi> :spec  
(new m) (B(l,m) | B(m,r))
where
B(i,o) = i(x).o<x>.B(i,o)
```

To see the top-level process:

```
Pi> :proc
(new m) (B(l,m) | B(m,r))
```

To apply the excommunication transformation to the current specification:
```
Pi> :transform  
l(x2).B7(l,r,x2)
where
B7(l,r,x2) = l(x3).r<x2>.B7(l,r,x3) + ([r=l]B7(l,r,x2) + r<x2>.l(x2).B7(l,r,x2))  
```

To quit from the program:

```
Pi> :quit
```

