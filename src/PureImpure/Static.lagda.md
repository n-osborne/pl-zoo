In this module, we define the syntax and the typing rules for the
language. We use dependant types as in Reuss & Altkentrich 1999
to make the term implicitly well-typed and the de Bruijn indexes
well-scoped by construction.

As we have some imperative features in the language, we add a the
information whether the term contains side effects in the type of its
definition.

```agda
module PureImpure.Static where

infix 10 _,_
infix  9 _∋_
infix  8 `!_
infix  7 _`→_ `λ_
infix  5 [_]_⊢_ _`$_ _`$!_
```

As a matter of type in the object language, we just need a type with
one uninteresting inhabitant (so, unit) to type side effects, the
natural numbers and functions.

```agda
data Ty : Set where
  `1 `N : Ty
  _`→_ : Ty -> Ty -> Ty
```
We define two status: pure and impure that correspond to the distinction
between expressions and statements.

```agda
data Status : Set where
  `pure `impure : Status
```

A typing context is a list of types as we use de Bruijn indexes.
The choice of a snoc constructor in place of cons is based solely on
aesthetic reasons (it's the way typing contexts are written on paper).

```agda
data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> Ty -> Ctx
```

In order to make our types lighter, let's define some variable.

```agda
variable
  Γ Δ : Ctx
  τ σ : Ty
  ζ ξ : Status
```

De Bruijn indexes are represented by a membership proof of the type of
the variable in the typing context of the term. Therefore, they are
well-scoped by construction.

```agda
data _∋_ : Ctx -> Ty -> Set where
  here : Γ , τ ∋ τ
  there : Γ ∋ τ -> Γ , σ ∋ τ
```

Now we can define our terms as a inductive type family indexed by a
status (does the term contains side efects?), the typing context and
the type of the term.

```agda
data [_]_⊢_ : Status -> Ctx -> Ty -> Set where

```

The language has builtin peano natural numbers.

```agda
  `Z :
    ------------
    [ `pure ] Γ ⊢ `N
    
  `S :
    [ `pure ] Γ ⊢ `N
    ---------------
    -> [ `pure ] Γ ⊢ `N
```

We want to be able to do case analysis on a natural number. In the case
that the natural is not zero, the case term evaluate to a term that is valid
with the same context in which the predecessor is added.

As the information about the status (pure/impure, *ie*
expression/statement) is coded by an index of the type (in the host
language), the case term can be pure or impure depending of the status
of the branches (which need to be the same).

```agda
  `case_[Z_|S_] :
    [ `pure ] Γ ⊢ `N
    -> [ ζ ] Γ ⊢ τ
    -> [ ζ ] Γ , `N ⊢ τ
    --------------
    -> [ ζ ] Γ ⊢ τ
```

We also define a conditional expression with the same caracteristic
*wrt* the status.

```agda
  `if_`then_`else_ :
    [ `pure ] Γ ⊢ `N
    -> [ ζ ] Γ ⊢ τ
    -> [ ζ ] Γ ⊢ τ
    ---------
    -> [ ζ ] Γ ⊢ τ
```

We define function by lambda abstraction.
A lambda abstraction is pure because it is a value (normal form),
even if its body can be impure.

```agda
  `λ_ :
    [ ζ ] Γ , τ ⊢ σ
    -------------------
    -> [ `pure ] Γ ⊢ τ `→ σ
```

Application of an anonym function. This is impure as the body of the
function can contain side effects that will affect the callee's
environment.

```agda
  _`$_ :
    [ `pure ] Γ ⊢ τ `→ σ
    -> [ `pure ] Γ ⊢ τ
    ------------------
    -> [ `impure ] Γ ⊢ σ -- ?
```

Application of a named function. This is pure because it won't affect
the callee's environment (the named function is a closure and come with its
own environment in which will happen the possible side effects).

```agda
  _`$!_ :
    Γ ∋ (τ `→ σ)
    -> [ `pure ] Γ ⊢ τ
    --------------
    -> [ `pure ] Γ ⊢ σ

```

The let binder takes a pure expression and a term (pure or impre) in
which this expression is available. The while term is impure (due to
the variable declaration and assignation).

```agda
  `let_`in_ :
    [ `pure ] Δ ⊢ τ
    -> [ ζ ] Γ , τ ⊢ σ
    ----------------
    -> [ `impure ] Γ ⊢ σ
```

Assignation follow the same logic but does not add a new variable to
the context. Assignation is of type `1.

```agda
  _`←_ :
    Γ ∋ τ
    -> [ `pure ] Δ ⊢ τ
    -----------------
    -> [ `impure ] Γ ⊢ `1

```

Reading a variable has no side effect.

```agda
  `!_ :
    Γ ∋ τ
    -------------
    -> [ `pure ] Γ ⊢  τ

```

We can put assignation in sequence.

```agda
  _`,_ :
    [ `impure ] Γ ⊢ `1
    -> [ ζ ] Γ ⊢ σ
    -----------------
    -> [ `impure ] Γ ⊢ σ

```

The while loop takes a pure expression evaluating to a natural number
as condition and one or several assignation.

```agda
  `while_`do_ :
    [ `pure ] Γ ⊢ `N
    -> [ `impure ] Γ ⊢ `1
    ------------------
    -> [ `impure ] Γ ⊢ `1

```

So, we will need to put a stop to a sequence of assignations.

```agda
  `done : -- aka skip
    --------------
    [ `impure ] Γ ⊢ `1 -- should I provide one pure ?

```
