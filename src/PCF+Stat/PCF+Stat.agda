module PCF+Stat.PCF+Stat where

infix 10 _,_
infix  9 _`→_
infix  8 `st_
infix  7 _∋_ _⊢_
infix  5 _`$_

data Ty : Set where
  `N `1 : Ty
  `st_ : Ty -> Ty
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
    
  `S : ∀ {Γ}
    -> Γ ⊢ `N
    ---------
    -> Γ ⊢ `N
    
  `λ : ∀ {Γ τ σ}
    -> Γ , σ ⊢ τ
    -------------
    -> Γ ⊢ σ `→ τ
    
  `case_[Z_|S_] : ∀ {Γ τ}
    -> Γ ⊢ `N      -- takes a nat
    -> Γ ⊢ τ       -- if zero, reduce to this expr 
    -> Γ ⊢ `N `→ τ -- if not, apply the pred to this function
    --------------
    -> Γ ⊢ τ
    
  `μ : ∀ {Γ τ}
    -> Γ ⊢ τ
    --------
    -> Γ ⊢ τ
    
  _`$_ : ∀ {Γ τ σ}
    -> Γ ⊢ σ `→ τ
    -> Γ ⊢ σ
    ---------
    -> Γ ⊢ τ
    
  `let : ∀ {Γ τ}
    -> Γ ⊢ τ
    ------------
    -> Γ ⊢ `st τ
    
  _`←_ : ∀ {Γ τ}
    -> Γ ∋ τ
    -> Γ ⊢ τ
    ---------
    -> Γ ⊢ `1
    
  `!_ : ∀ {Γ τ}
    -> Γ ∋ τ
    --------
    -> Γ ⊢ τ
    
  _`,_ : ∀ {Γ τ σ}
    -> Γ ⊢ `st τ  -- declare a new var
    -> Γ , τ ⊢ σ  -- following exp should be valid with this new var in the Ctx
    -------------
    -> Γ ⊢ σ
    
  _`,,_ : ∀ {Γ τ}
    -> Γ ⊢ `1  -- assign a new value to an existing var
    -> Γ ⊢ τ   -- then continue the expression
    ---------
    -> Γ ⊢ τ
    
  `while_`do_ : ∀ {Γ}
    -> Γ ⊢ `N  -- loop condition
    -> Γ ⊢ `1  -- loop body just change value of existing var
    ----------
    -> Γ ⊢ `1  -- while expression does not have interesting value
