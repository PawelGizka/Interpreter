Intepreter of my own programming language. 

My language is imperative, statically typed with some features from
functional languages.

Grammer is based mainly on: Scala and Javascript (function closures)

In my.ebnf file is complete language grammar.   

Some of language features:
- first class functions: functions as parameters, closures, reasigments to functions,
returning functions as arguments,
- arrays,
- garbage collection,
- static scopes,
- static type checking,

Examples of programs can be found in programs subdirectory.

Interpreter is written in monadic style with use of monad transformers.

Program state is divided into environments and one global store.
Every function has its own environment. 

Garbage collection procedure is launched after every 1000000 insertion to store.
It marks all available locations in store (including locations referenced by closures and arrays)
and removes not marked.

Compile:
```make```

Launch:
```./interpreter programFile```

Pass arguments:
```./interpreter programFile argument1 argument2 ...```

For example:
```./interpreter programs/hello```
