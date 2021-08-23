# An Interpreter for the untyped-lambda calculus


A simple intepreter for evaluating lambda terms. In order to execute the interpreter, just 
use the Haskell stack:


```
stack exec lambda-exe
```

which will start the intepreter prompt. The intepreter has two commands

- `quit`: Finishes the intepreter execution.

- `show-defs`: Show the definitions in the current interpreter execution.

We can create new definitions as follows:

```
false = \ x y . y
```

The basic syntax for definitions is `ID = TERM`, where

- `ID`: is a valid identifier.

- `TERM`: is a valid lambda term.


