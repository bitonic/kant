Bertus is a small language with dependent types, written to explore possible ways
to implement a core language supporting
[observational equality](http://www.cs.nott.ac.uk/~txa/publ/obseqnow.pdf).

Current features include:

  * User defined data types and records
  * Implicit universe hierarchy
  * Bidirectional type checking for abstractions
  * Type holes

Planned features are:

  * Observational equality
  * Inference via pattern unification

Other 'possible' features:

  * Pattern matching
  * Corecursion

## Brief overview

### Syntax

Let's see... you have functions:

    \x y => ...

In this case with the arguments left untyped, which means that the term
must be checkable---e.g. the argument of an application.  If the term is
not checkable you can type the function explicitly:

    \[x : A][y : B] : C => ...

Where @C@ is the return type.  Then you obviously have application

    x y z === (x y) z

For what concerns declarations, there are 4 kinds.  The two simple ones
are values and postulated variables.  Values can be declared like so:

    name [x : A] [y : A] : C => ...

where @x@ and @y@ will be named arguments, and @C@ is the return type.
You can also 'postulate' variables:

    postulate name : A

### Inductive data and records

Data types are declared like so:

    data Name : A => { con1 : C1 | con2 : C2 | ... }

where @A@ is the type of the type constructor, and thus must be formed
by named parameters returning @*@; and each constructor has a type which
must return @Name pars@, where @pars@ are the name parameters.

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
@Name-Elim@.

You can also define records:

    record Tuple : [A : *] [B : A -> *] =>
      tuple { fst : A | snd : B fst }

here we define the one data constructor (@tuple@) and the fields (@fst@
and @snd@).  Note that fields can refer to previous fields in their
type.  @fst@ and @snd@ will serve as projections, extracting data from
elements of @Tuple@.

Note that constructors and eliminators are not 'normal' functions, like
in Haskell.  To perform bidirectional type checking, constructors must
be applied to all their arguments to be used, and eliminators to the
'eliminated'.

### Type holes

...

### Type hierarchy

...
