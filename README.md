# Excommunicator
Transformation Tool to Remove Internal Communication from Pi-Calculus Processes using the
Blazed Excommunication Algorith as described in the paper "Excommunication: Transforming Pi-Calculus Specifications to Remove Internal Communication"

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
l(x'').B''(l,r,x'')
where
B''(l,r,x'') = l(x''').r<x''>.B''(l,r,x''') + ([r=l]B''(l,r,x'') + r<x''>.l(x'').B''(l,r,x''))  
```

To quit from the program:

```
Pi> :quit
```

