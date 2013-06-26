Naming
======================================================================

Bertus was originally Kant.  We haven't changed the naming everywhere
yet.

Building/Installing
======================================================================

To build bertus, you need to have a recent [Haskell
Platform](http://www.haskell.org/platform/).  Once you have that you can
simply run

    $ cabal install

in this directory, and wait.  If you just want to build, type

    $ cabal configure

take note of the libraries you need (if any, and install them), then
configure again and

    $ cabal build

Running
======================================================================

The CLI interpreter can be run with

    $ ./kant.sh

The web application can be run with

    $ ./kant-web.sh -b <bind-address> -p <port-number>

Without arguments it will run on `127.0.0.1:8000`.

Using
======================================================================

Check `data/docs/overview.md` for a brief description of the language.

Source code overview
======================================================================

Here is an overview of the modules.

You can also run `./modules.sh` to generate a `modules.pdf` file with a
dependency graph---you will need [dot](http://www.graphviz.org/) and
[graphmod](http://hackage.haskell.org/package/graphmod).

````
Data.
  Bwd          A simple backward list type, useful when building up
               lists of variables

  LGraph       A module for labelled graphs, we need it for Constraint

  Constraint   A module to handle check the consistency of a set of
               constraints, we use it to implement the implicit
               hierarchy.

Kant.
  Common       Assorted functions, mostly to re-define
               Functor/Applicative operators in terms of Monad---we
               don't want many constraints in type sigs.

  Term         Define the basic term type, `Tm', along with several
               operations on it.

  Cursor       Defines a data structure to traverse the term while being
               able to convert every variable back to a string and
               carrying a context.

  Decl         Defines the syntax for declarations.

  ADT          Defines the data structures that hold the elaborated
               declarations in the environments.

  Env          Defines a Cursor on steroids that we carrry around
               everywhere.  It holds ADTs, a context for the types of
               bound variables, and a generator of fresh references for
               various purposes.

  Ref          Decorates each occurence of `*` (the type of types) with
               a unique reference.  This is to implement the automatic
               hierarchy consistency check.

  ConDestr     Transforms applications of data constructors and
               eliminators to a special form.  Needed to implement
               bidirectional type checking.

  Reduce       Reduces terms to their normal or weak head normal form.

  Prelude      Defines some names referencing things defined in
               `data/prelude.ka'

  Error        Defines a data type to describe what can go wrong at
               any point.  Coarse but effective.

  Monad        Defines a monad where we execute stateful/errorful
               operations---we can retrieve the `Kant.Env' and throw
               `Kant.Error's.

  TyCheck      The type checker.

  Elaborate    The messy bit.  Turns `Kant.Decl' into types and
               rewriting rules stored in a `Kant.ADT', which is in turn
               stored in a `Kant.Env'.

  Sugar        Defines the syntax that the user types in, a fancier,
               explicitly named version of the `Data.Term'.

  Lexer        Tokenises the text input.

  Parser       Turns tokens into `Kant.Sugar'.

  Desugar      Turns `Kant.Sugar' into a `Kant.Term'.

  Uniquify     Turns a nested `Kant.Term' into a top-level one, with
               fresh names.

  Distill      Turns a `Kant.Term' into a `Kant.Sugar'.  The inverse
               of `Kant.Desugar'.

  REPL         Brings it all together by defining a little monadic
               state machines that processes user commands and spits
               output.
````

Additionally, the executable for the CLI prompt is in `kant.hs`, and the
web one in `kant-web.hs`.
