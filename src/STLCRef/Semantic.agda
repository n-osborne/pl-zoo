module STLCRef.Semantic where

import Utils.Ctx as CtxM

infix  17 `V_
infixr 16 _`$_
infix  15 `ref_ `!_
infix  9  _⊢_
infixl 10 _`→_
infix   8 `S_

data Ty : Set where
  `1 `N : Ty
  `ref_ : Ty -> Ty
  _`→_  : Ty -> Ty -> Ty

open module Ctx = CtxM Ty

private
  variable
    Γ Δ : Ctx
    τ σ : Ty
    
data _⊢_ : Ctx -> Ty -> Set where

  `done :
    -------
    Γ ⊢ `1

  `Z :
    -------
    Γ ⊢ `N

  `S_ :
    Γ ⊢ `N
    ----------
    -> Γ ⊢ `N

  `λ_ :
    Γ , σ ⊢ τ
    -------------
    -> Γ ⊢ σ `→ τ

  _`$_ :
    Γ ⊢ σ `→ τ
    -> Γ ⊢ σ
    --------
    -> Γ ⊢ τ

  `V_  :
    Γ ∋ τ
    --------------
    -> Γ ⊢ `ref τ

  `!_  :
    Γ ⊢ `ref τ
    -----------
    -> Γ ⊢ τ 

  `let_`in_ :
    Γ ⊢ σ
    -> Γ , σ ⊢ τ
    -------------
    -> Γ ⊢ τ

  _`←_ :
    Γ ⊢ `ref τ
    -> Γ ⊢ τ
    ----------
    -> Γ ⊢ `1

  _`,_ :
    Γ ⊢ `1
    -> Γ ⊢ τ
    ---------
    -> Γ ⊢ τ
