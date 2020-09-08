module PureImpure.Static where

infix 10 _,_
infix  9 _∋_
infix  8 `!_
infix  7 _`→_ `λ_
infix  6 `pure_ `impure_
infix  5 _⊢_ _`$_ _`$$_

data PreTy : Set where
  `1 `N : PreTy
  _`→_ : PreTy -> PreTy -> PreTy

data Ty : PreTy -> Set where
  `pure_ `impure_ : (τ : PreTy) -> Ty τ

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> PreTy -> Ctx

variable
  Γ Δ : Ctx
  τ σ : PreTy

_⊔_ : Ty τ -> Ty τ -> Ty τ
(`pure τ)   ⊔ (`pure _)   = `pure τ
(`pure τ)   ⊔ (`impure _) = `impure τ
(`impure τ) ⊔ (`pure _)   = `impure τ
(`impure τ) ⊔ (`impure _) = `impure τ

data _∋_ : Ctx -> PreTy -> Set where
  here : Γ , τ ∋ τ
  there : Γ ∋ τ -> Γ , σ ∋ τ

data _⊢_ : Ctx -> Ty τ -> Set where

  `Z :
    ------------
    Γ ⊢ `pure `N
    
  `S :
    Γ ⊢ `pure `N
    ---------------
    -> Γ ⊢ `pure `N
    
  `case_[Z_|S_] :
    ∀ {φ : Ty σ}
    -> Γ ⊢ `pure `N
    -> Γ ⊢ φ
    -> Γ , `N ⊢ φ
    --------------
    -> Γ ⊢ φ
    
  `if_`then_`else_ :
    ∀ {φ : Ty σ}
    -> Γ ⊢ `pure `N
    -> Γ ⊢ φ
    -> Γ ⊢ φ
    ---------
    -> Γ ⊢ φ

  `ret :
    Γ ⊢ `impure τ
    ----------------
    -> Γ ⊢ `pure τ

  `λ_ :
    ∀ {φ : Ty σ}
    -> Γ , τ ⊢ φ
    -------------------
    -> Γ ⊢ `pure τ `→ σ
    
  _`$_ :
    Γ ⊢ `pure (τ `→ σ)
    -> Γ ⊢ `pure τ
    ------------------
    -> Γ ⊢ `impure σ -- ?

  _`$$_ :
    Γ ∋ (τ `→ σ)
    -> Γ ⊢ `pure τ
    --------------
    -> Γ ⊢ `pure σ
    
  `let_`in_ :
    ∀ {φ : Ty σ}
    -> Δ ⊢ `pure τ
    -> Γ , τ ⊢ φ
    ----------------
    -> Γ ⊢ `impure σ
    
  _`←_ :
    Γ ∋ τ
    -> Δ ⊢ `pure τ
    -----------------
    -> Γ ⊢ `impure `1

  `!_ :
    Γ ∋ τ
    -------------
    -> Γ ⊢ `pure τ

  _`,_ :
    ∀ {φ : Ty σ}
    -> Γ ⊢ `impure `1
    -> Γ ⊢ φ
    -----------------
    -> Γ ⊢ `impure σ

  `while_`do_ :
    Γ ⊢ `pure `N
    -> Γ ⊢ `impure `1
    ------------------
    -> Γ ⊢ `impure `1

  `done :
    --------------
    Γ ⊢ `impure `1
