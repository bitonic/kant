Bertus is a small language with dependent types, written to explore possible ways
to implement a core language supporting
[observational equality](http://www.cs.nott.ac.uk/~txa/publ/obseqnow.pdf).

Current features include:

  * User defined data types and records;
  * Implicit universe hierarchy;
  * Bidirectional type checking, both for abstraction and user defined types;
  * Type holes.

Half done features:

  * Observational equality
    
    We have put the foundations---syntax and typing rules---but we lack
    the reduction rules and quotation.

Planned features are:

  * Pattern matching and explicit recursion;
  * Inference via pattern unification;
  * Corecursion.

## Warning

Bertus should be pretty solid but it's just a beginning.  Error messages
will be ugly, and in general the system is not meant to be used yet for
'proper' programming or theorem proving.

Moreover, the parser will accept things that it cannot typecheck
(because I haven't implemented OTT yet) and crash.  If you get a
WebSocket error, that's what happened.  Don't worry, the server is still
running.

## Using the REPL

Type `:h`, then your return key, and keep reading there.  You can load
all the files in the
[examples](https://github.com/bitonic/kant/tree/master/data/samples).
In the command line REPL you can load whatever you want, obviously.

## Brief overview

Francesco, go write proper docs!

### Syntax

The best thing is to head towards the few
[examples](https://github.com/bitonic/kant/tree/master/data/samples) I
have put together, good and bad.

Let's see... you have functions:

    \x y => ...

In this case with the arguments left untyped, which means that the term
must be checkable---e.g. the argument of an application.  If the term is
not checkable you can type the function explicitly:

    \[x : A][y : B] : C => ...

Where `C` is the return type.  Then you obviously have application

    x y z === (x y) z

You also have the type of types, `*`.  There is a hierarchy but it is
cumulative and it is hidden from you, so don't you worry about that.

For what concerns declarations, there are 4 kinds.  The two simple ones
are values and postulated variables.  Values can be declared like so:

    name [x : A] [y : A] : C => ...

where `x` and `y` will be named arguments, and `C` is the return type.
You can also 'postulate' variables:

    postulate name : A

For the other 2 declarations, head to the next section.

### Inductive data and records

Data types are declared like so:

    data Name : A => { con1 : C1 | con2 : C2 | ... }

where `A` is the type of the type constructor, and thus must be formed
by named parameters returning `*`; and each constructor has a type which
must return `Name pars`, where `pars` are the type parameters.

Some examples:

    data Nat : * => { zero : Nat | suc : Nat -> Nat }

    data Maybe : [A : *] -> * =>
      { nothing : Maybe A | just : A -> Maybe A }

    nonZero [n : Nat]   : * => ...
    eq      [n m : Nat] : * => ...

    data Fin : [n : Nat] -> * =>
      { fzero : nonZero n -> Fin n
      | fsuc  : [n' : Nat] -> Fin n' -> eq n n' -> Fin 
      }

An 'eliminator' is associated with each inductive data type,
corresponding to its induction principle.  The eliminator will be named
`Name-Elim`.

You can also define records:

    record Tuple : [A : *] [B : A -> *] =>
      tuple { fst : A | snd : B fst }

here we define the one data constructor (`tuple`) and the fields (`fst`
and `snd`).  Note that fields can refer to previous fields in their
type.  `fst` and `snd` will serve as projections, extracting data from
elements of `Tuple`.

Note that constructors and eliminators are not 'normal' functions, like
in Haskell.  To perform bidirectional type checking, constructors must
be applied to all their arguments to be used, and eliminators to the
'eliminated'.

### Type holes

> I've got 99 holes but a proof ain't one.
> <cite> Jay 'Well-Order' Z </cite>

We have rudimentary holes, of the type kind.  You can barely see through
them.  A hole is a place holder for a term:

    {| hole-name term1 term2 ... |}

When put somewhere, Bertus will tell you what type is expected for
`hole-name` and what is the type of all the terms in `hole-name`.
