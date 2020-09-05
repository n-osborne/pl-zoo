```agda

module PCF+While.Static where
```

In this module we define the syntax and the static semantic (typing
rules) for a small language (basically PCF + While).

As showed in Reuss and Alkentritch 1999, we make use of dependent
types to have a terms implicitly typed and de Bruijn indexes
implicitly well-scoped. We want to adapt this technique to a
programming language with imperative features (namely mutable variable
and a while loop).

```agda

infix 10 _`→_
infix  9 _,_
infix  8 `S_ 
infix  7 _∋_ _⊢_
infix  5 _`$_ `λ_ `μ_

```

We don't want too much types in our language (that's not the
point). We will be happy with natural numbers, a type with only one
uninteresting value to type side-effects (asignations) and functions.

For the sake of readability, we prefixe all the constants of the object
language with a back tick.


```agda

data Ty : Set where
  `N `1 : Ty
  _`→_ : Ty -> Ty -> Ty

```

We will need typing context. With the way we code de Bruijn indexes, a
typing context is just a list of types. We choose a snoc constructor
in place of the traditional cons, but it is just a matter of
aesthetics.

```agda

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> Ty -> Ctx

```

Then, de Bruijn indexes are proof of membership of the type in the
typing context. So a de Bruijn index is well-scoped by construction
and it bears its type with itself.

Again, we use a reversed membership operator for aesthetics reasons:
it is in the some order as the term type that we use which is the
typing judgment symbol.

```agda

data _∋_ : Ctx -> Ty -> Set where
  here : ∀ {Γ τ} -> Γ , τ ∋ τ
  there : ∀ {Γ τ σ} -> Γ ∋ τ -> Γ , σ ∋ τ

```

We can now define the implicitly typed syntax of our small
language. We will informally provide the intended semantic.

```agda

data _⊢_ : Ctx -> Ty -> Set where

```

Let's start with the natural numbers. We will only need Peano natural
numbers. So we have a builtin and pretty straightforward zero and
successor constructors.

```agda

  `Z : ∀ {Γ}
    ----------
    -> Γ ⊢ `N
    
  `S_ : ∀ {Γ}
    -> Γ ⊢ `N
    ---------
    -> Γ ⊢ `N

```

Then, we will want to do case split on natural numbers. This term
constructor takes a natural number, the term to which is should
evaluate if this natural number is zero, and finally, what to do with
the predecessor if the natural number is not zero. So the third
argument is a term that have a function type from `N to whatever is
the type of the whole expression.

We can see here that we can enforce the typing rules of the object
language using Agda's typechecker.

```agda

  `case_[Z_|S_] : ∀ {Γ τ}
    -> Γ ⊢ `N
    -> Γ ⊢ τ
    -> Γ ⊢ `N `→ τ
    --------------
    -> Γ ⊢ τ

```

Then we have lambda abstraction and application, which are pretty
straightforwards. Here again, the coherence of the types in the object
language is checked by Agda.

As this is just a small language that will not be used to do any real
programming, we don't bother with anything else that 1-ary functions.

That being said, as we will be able to bind a function to a variable,
we need to keep in mind that we will use closure to store the said
function.

```agda

  `λ_ : ∀ {Γ τ σ}
    -> Γ , σ ⊢ τ
    -------------
    -> Γ ⊢ σ `→ τ
    
  _`$_ : ∀ {Γ τ σ}
    -> Γ ⊢ σ `→ τ
    -> Γ ⊢ σ
    ---------
    -> Γ ⊢ τ

```

We also want general recursivity, which is just self application.

```agda

  `μ_ : ∀ {Γ τ}
    -> Γ , τ ⊢ τ
    ------------
    -> Γ ⊢ τ

```

Now we can turn to declarations and assignations.

Declarations are done via a let binding. The constructor of a let
binding takes the value assigned to the new variable and the term in
which this new variable is in scope. In this term, the new variable is
binded to the de Bruijn index corresponding to 0.

As the new value can be the result of a function call, that is the
evaluation of a closure together with its argument, we need the
possibility that this term is valid in another context.

```agda
    
  `let_`in_ : ∀ {Γ Δ τ σ}
    -> Δ ⊢ σ
    -> Γ , σ ⊢ τ
    ------------
    -> Γ ⊢ τ

  `!_ : ∀ {Γ τ}
    -> Γ ∋ τ
    --------
    -> Γ ⊢ τ

```

Once a variable is declared, a value is binded to it. As the variables
are mutable, we can change this value. In order to do so, we need the
de Bruijn index, so that we can identify which variable has its value
changed. We also need the new value. As in the assignation, the term
for the value need not to be valid in the same context as the actual
context.

```agda

  _`←_ : ∀ {Γ Δ τ}
    -> Γ ∋ τ
    -> Δ ⊢ τ
    ---------
    -> Γ ⊢ `1

```

Then, we want to put assignations in sequence, building a term that evaluate
to something of type τ.

```agda

  _`,_ : ∀ {Γ τ}
    -> Γ ⊢ `1
    -> Γ ⊢ τ
    ---------
    -> Γ ⊢ τ

```

Now, we can have while loops. The condition is a natural number. We
skip the body of the loop if the condition is zero and we evaluate the
body if the condition is not zero.

The body of the loop is of type `1, that is it does not evaluate to an
interesting value. We are just interested by the side effects occuring
in the body of the loop.

```agda

  `while_`do_ : ∀ {Γ}
    -> Γ ⊢ `N
    -> Γ ⊢ `1
    ---------
    -> Γ ⊢ `1

```

So we will need to signal the end of a sequence of statements (terms
of type `1). We call it `done.

```agda

  `done : ∀ {Γ}
    -----------
    -> Γ ⊢ `1

```
