module WhileRec.WellScopedSyntax where

infixr 8 `V_ there_
infixr 7 `S_ `λ_ `fix_ `!_
infixl 6 _`$_
infixr 4 _`←_,,_ `while_`do_,,_ `let_,,_
infix  3 _⊢_ _∋_

open import WhileRec.Ty

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Ty -> Ctx

data _∋_ : Ctx -> Ty -> Set where
  here : ∀ {Γ τ} -> Γ , τ ∋ τ 
  there_ : ∀ {Γ τ σ} -> Γ ∋ τ -> Γ , σ ∋ τ

-- _≤_ : ∀ {Γ τ σ} -> Γ ∋ τ -> Γ ∋ σ -> Set
-- here ≤ q = ⊤
-- (there p) ≤ here = ⊥
-- (there p) ≤ (there q) = p ≤ q

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

  `V_ : ∀ {Γ τ}
    -> Γ ∋ τ
    --------
    -> Γ ⊢ `ref τ

  `!_ : ∀ {Γ τ}
    -> Γ ⊢ `ref τ
    -------------
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
    -> Γ ⊢ `ref τ
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
n `-1 = `λ `case `! `V here [Z `! `V here |Sn `! `V here ] `$ n
  
`plus-rec : ∀ {Γ} -> Γ ⊢ `N `⇒ `N `⇒ `N
`plus-rec = `fix `λ `λ `case `! `V here
                             [Z `! (`V (there here))
                             |Sn `S (`! (`V (there (there (there here)))) `$ `! `V (there (there here)) `$ `! `V here) ]

`plus-imp : ∀ {Γ} -> Γ ⊢ `N `⇒ `N `⇒ `N
`plus-imp = `λ `λ (`while `! `V here `do
                          `V here       `← (`! `V here) `-1 ,,
                          `V there here `← `S `! `V there here ,,
                          `done ,,
                  `! `V there here)

