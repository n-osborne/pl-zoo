```agda

module PCF+Stat.Static where


infix 10 _`→_
infix  9 _,_
infix  8 `S_ 
infix  7 _∋_ _⊢_
infix  5 _`$_ `λ_ `μ_

data Ty : Set where
  `N `1 : Ty
  _`→_ : Ty -> Ty -> Ty

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> Ty -> Ctx

data _∋_ : Ctx -> Ty -> Set where
  here : ∀ {Γ τ} -> Γ , τ ∋ τ
  there : ∀ {Γ τ σ} -> Γ ∋ τ -> Γ , σ ∋ τ

data _⊢_ : Ctx -> Ty -> Set where

  `done : ∀ {Γ}
    -----------
    -> Γ ⊢ `1
    
  `Z : ∀ {Γ}
    ----------
    -> Γ ⊢ `N
    
  `S_ : ∀ {Γ}
    -> Γ ⊢ `N
    ---------
    -> Γ ⊢ `N
    
  `λ_ : ∀ {Γ τ σ}
    -> Γ , σ ⊢ τ
    -------------
    -> Γ ⊢ σ `→ τ
    
  `case_[Z_|S_] : ∀ {Γ τ}
    -> Γ ⊢ `N      -- takes a nat
    -> Γ ⊢ τ       -- if zero, reduce to this expr 
    -> Γ ⊢ `N `→ τ -- if not, apply the pred to this function
    --------------
    -> Γ ⊢ τ
    
  `μ_ : ∀ {Γ τ}
    -> Γ ⊢ τ
    --------
    -> Γ ⊢ τ
    
  _`$_ : ∀ {Γ τ σ}
    -> Γ ⊢ σ `→ τ
    -> Γ ⊢ σ
    ---------
    -> Γ ⊢ τ
    
  `let_`in_ : ∀ {Γ τ σ} -- declare a new var
    -> Γ ⊢ σ            -- the value asigned to the new var
    -> Γ , σ ⊢ τ        -- the term in which this new var is in scope
    ------------
    -> Γ ⊢ τ
    
  _`←_ : ∀ {Γ τ} -- modify an existing var
    -> Γ ∋ τ     -- the de Bruijn index of the var
    -> Γ ⊢ τ     -- the new value
    ---------
    -> Γ ⊢ `1    -- whole expression does not have an interesting value
    
  _`,_ : ∀ {Γ τ} -- sequence an assignment and some other exp
    -> Γ ⊢ `1     -- assign a new value to an existing var
    -> Γ ⊢ τ      -- then continue the expression
    ---------
    -> Γ ⊢ τ      -- whole expression has the type of the second member

  `!_ : ∀ {Γ τ}
    -> Γ ∋ τ
    --------
    -> Γ ⊢ τ

  `while_`do_ : ∀ {Γ}
    -> Γ ⊢ `N  -- loop condition
    -> Γ ⊢ `1  -- loop body just changes value of existing var
    ----------
    -> Γ ⊢ `1  -- while expression does not have interesting value
```
