module STLC+Ref.Semantic where

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

StoreTy = Ctx

private
  variable
    Σ Σ' : StoreTy
    
mutual

  data Val : StoreTy -> Ty -> Set where
     `Z-val  : Val Σ `N
     `S-val  : Val Σ `N -> Val Σ `N
     `λ⟨_,_⟩ : Γ , σ ⊢ τ -> Env Σ Γ -> Val Σ (σ `→ τ)

  Env : StoreTy -> Ctx -> Set
  Env Σ Γ = All (λ τ -> Val Σ τ) Γ

Store : StoreTy -> Set
Store Σ = Env Σ Σ

mutual
  lift-val : (σ : Ty) -> Val Σ τ -> Val (Σ , σ) τ
  lift-val σ `Z-val      = `Z-val
  lift-val σ (`S-val v)  = `S-val (lift-val σ v)
  lift-val σ `λ⟨ T , E ⟩ = `λ⟨ T , lift-env σ E ⟩

  lift-env : (σ : Ty) -> Env Σ Γ -> Env (Σ , σ) Γ
  lift-env σ CtxM.∅         = ∅
  lift-env σ (env CtxM., v) = lift-env σ env , lift-val σ v

store : ∀ {τ} -> Val Σ τ -> Store Σ -> Store (Σ , τ)
store {Σ}{τ} v st = lift-env τ st , lift-val τ v


