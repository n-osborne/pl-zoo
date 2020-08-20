module WhileRec.WellScopedSyntax where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; _≢_)
open import Relation.Nullary using (Dec; yes; no)


--infixr 8 there_
infixr 7 `S_ `λ_ `fix_ `!_
infixl 6 _`$_
infixr 4 _`←_,,_ `while_`do_,,_ `let_,,_
infix  3 _⊢_ _∋_

open import WhileRec.Ty hiding (_≟_)

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Ty -> Ctx

data _∋_ : Ctx -> Ty -> Set where
  here : ∀ {Γ τ} -> Γ , τ ∋ τ 
  there : ∀ {Γ τ σ} -> Γ ∋ τ -> Γ , σ ∋ τ

{--
postulate 
  aux : ∀ {Γ τ σ}{d₀ d₁ : Γ ∋ τ} -> d₀ ≢ d₁ -> (there {σ = σ} d₀) ≢ (there d₁)

_≟_ : ∀ {Γ τ} -> (db₀ : Γ ∋ τ) -> (db₁ : Γ ∋ τ) -> Dec (db₀ ≡ db₁)
here ≟ here = yes refl
here ≟ (there d₁) = no (λ ())
(there d₀) ≟ here = no (λ ())
(there d₀) ≟ (there d₁) with d₀ ≟ d₁
(there d₀) ≟ (there d₁) | yes p rewrite p = yes refl
(there d₀) ≟ (there d₁) | no ¬p = no (aux ¬p)
--}

data _⊢_ : Ctx -> Ty -> Set where

  `done : ∀ {Γ}
    ---------
    -> Γ ⊢ `1

  `Z : ∀ {Γ}
    ----------
    -> Γ ⊢ `N

  `S_ : ∀ {Γ}
    -> (n : Γ ⊢ `N)
    ---------------
    -> Γ ⊢ `N

  `!_ : ∀ {Γ τ}
    -> Γ ∋ τ
    ---------
    -> Γ ⊢ τ

  `λ_ : ∀ {Γ τ σ}
    -> Γ , τ ⊢ σ
    ------------
    -> Γ ⊢ τ `⇒ σ
  
  _`$_ : ∀ {Γ τ σ}
    -> Γ ⊢ τ `⇒ σ
    -> Γ ⊢ τ
    --------
    -> Γ ⊢ σ

  `fix_ : ∀ {Γ τ}
    -> Γ , τ ⊢ τ
    ------------
    -> Γ ⊢ τ
    
  `let_,,_ : ∀ {Γ τ σ}
    -> Γ ⊢ τ
    -> Γ , τ ⊢ σ
    ------------
    -> Γ ⊢ σ

  _`←_,,_ : ∀ {Γ τ σ}
    -> Γ ∋ τ
    -> Γ ⊢ τ
    -> Γ ⊢ σ
    --------
    -> Γ ⊢ σ

  `case_[Z_|Sn_] : ∀ {Γ τ}
    -> Γ ⊢ `N
    -> Γ ⊢ τ
    -> Γ , `N ⊢ τ
    -------------
    -> Γ ⊢ τ

  `while_`do_,,_ : ∀ {Γ τ}
    -> Γ ⊢ `N
    -> Γ ⊢ `1
    -> Γ ⊢ τ
    --------
    -> Γ ⊢ τ


_`-1 : ∀ {Γ} -> Γ ⊢ `N -> Γ ⊢ `N
n `-1 = `λ `case `! here [Z `! here |Sn `! here ] `$ n
  
`plus-rec : ∀ {Γ} -> Γ ⊢ `N `⇒ `N `⇒ `N
`plus-rec = `fix `λ `λ `case `! here
                             [Z `! (there here)
                             |Sn `S (`! (there (there (there here))) `$ `! there (there here) `$ `! here) ]

`plus-imp : ∀ {Γ} -> Γ ⊢ `N `⇒ `N `⇒ `N
`plus-imp = `λ `λ (`while `! here `do
                          here       `← (`! here) `-1 ,,
                          there here `← `S `! there here ,,
                          `done ,,
                  `! there here)

