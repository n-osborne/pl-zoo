module PureImpure.Static where

infix 10 _,_
infix  9 _∋_
infix  8 `!_
infix  7 _`→_ `λ_
infix  5 [_]_⊢_ _`$_ _`$$_

data Ty : Set where
  `1 `N : Ty
  _`→_ : Ty -> Ty -> Ty

data Status : Set where
  `pure `impure : Status

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> Ty -> Ctx

variable
  Γ Δ : Ctx
  τ σ : Ty
  ζ ξ : Status

data _∋_ : Ctx -> Ty -> Set where
  here : Γ , τ ∋ τ
  there : Γ ∋ τ -> Γ , σ ∋ τ

data [_]_⊢_ : Status -> Ctx -> Ty -> Set where

  `Z :
    ------------
    [ `pure ] Γ ⊢ `N
    
  `S :
    [ `pure ] Γ ⊢ `N
    ---------------
    -> [ `pure ] Γ ⊢ `N
    
  `case_[Z_|S_] :
    [ `pure ] Γ ⊢ `N
    -> [ ζ ] Γ ⊢ τ
    -> [ ζ ] Γ , `N ⊢ τ
    --------------
    -> [ ζ ] Γ ⊢ τ
    
  `if_`then_`else_ :
    [ `pure ] Γ ⊢ `N
    -> [ ζ ] Γ ⊢ τ
    -> [ ζ ] Γ ⊢ τ
    ---------
    -> [ ζ ] Γ ⊢ τ

-- seems to be needed to assign the result of a function call to a var
-- but raises problems
-- it is now possible to write : `let (`ret (impure expr)) `in T

  `ret :
    [ ζ ] Γ ⊢ τ
    ----------------
    -> [ `pure ] Γ ⊢ τ

  `λ_ :
    [ ζ ] Γ , τ ⊢ σ
    -------------------
    -> [ `pure ] Γ ⊢ τ `→ σ
    
  _`$_ :
    [ `pure ] Γ ⊢ τ `→ σ
    -> [ `pure ] Γ ⊢ τ
    ------------------
    -> [ `impure ] Γ ⊢ σ -- ?

  _`$$_ :
    Γ ∋ (τ `→ σ)
    -> [ `pure ] Γ ⊢ τ
    --------------
    -> [ `pure ] Γ ⊢ σ
    
  `let_`in_ :
    [ `pure ] Δ ⊢ τ
    -> [ ζ ] Γ , τ ⊢ σ
    ----------------
    -> [ `impure ] Γ ⊢ σ
    
  _`←_ :
    Γ ∋ τ
    -> [ `pure ] Δ ⊢ τ
    -----------------
    -> [ `impure ] Γ ⊢ `1

  `!_ :
    Γ ∋ τ
    -------------
    -> [ `pure ] Γ ⊢  τ

  _`,_ :
    [ `impure ] Γ ⊢ `1
    -> [ ζ ] Γ ⊢ σ
    -----------------
    -> [ `impure ] Γ ⊢ σ

  `while_`do_ :
    [ `pure ] Γ ⊢ `N
    -> [ `impure ] Γ ⊢ `1
    ------------------
    -> [ `impure ] Γ ⊢ `1

  `done : -- aka skip
    --------------
    [ `impure ] Γ ⊢ `1 -- should I provide one pure ?
