module PCF+Stat.PCF+Stat where

infix 10 _`→_
infix  9 _,_
infix  8 `st_ `S_ 
infix  7 _∋_ _⊢_
infix  5 _`$_ `λ_ `μ_
infix  3 _⟶_

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
    
  `let_`in_ : ∀ {Γ τ} -- declare a new var
    -> Γ ⊢ `N         -- the value asigned to the new var
    -> Γ , `N ⊢ τ     -- the term in which this new var is in scope
    ------------
    -> Γ ⊢ τ

  `fun_`in_ : ∀ {Γ τ σ υ}
    -> Γ ⊢ τ `→ σ
    -> Γ , τ `→ σ ⊢ υ
    -----------------
    -> Γ ⊢ υ
    
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

mutual

  data Val : Ty -> Set where
    v-Z :
      Val `N
      
    v-S :
      Val `N
      ---------
      -> Val `N
      
    v-⟨_,_⟩ :
      ∀ {Γ τ σ}
      -> Store Γ
      -> Γ , τ ⊢ σ      
      ---------------
      -> Val (τ `→ σ)

  data Store : Ctx -> Set where
    ∅   : Store ∅
    _,_ : ∀ {Γ τ} -> Store Γ -> Val τ -> Store (Γ , τ)

getCtx : ∀ {τ σ} ->  Val (τ `→ σ) -> Ctx
getCtx (v-⟨_,_⟩ {Γ} _ _) = Γ

getStore : ∀ {τ σ} -> (v : Val (τ `→ σ)) -> Store (getCtx v)
getStore v-⟨ Σ , _ ⟩ = Σ

getBody : ∀ {τ σ} -> (v : Val (τ `→ σ)) -> (getCtx v) , τ ⊢ σ
getBody v-⟨ _ , b ⟩ = b

data Storable : ∀ {Γ τ} -> Γ ⊢ τ -> Set where
  st-Z : ∀ {Γ} -> Storable (`Z {Γ})
  st-S : ∀ {Γ}{n : Γ ⊢ `N} -> Storable n -> Storable (`S n)
  st-λ : ∀ {Γ τ σ} -> (t : Γ , τ ⊢ σ) -> Storable (`λ t)

_!_ : ∀ {Γ τ} -> Γ ∋ τ -> Store Γ -> Val τ
here ! (_ , v)    = v
there p ! (Σ , _) = p ! Σ

update : ∀ {Γ τ} -> Γ ∋ τ -> Store Γ -> Val τ -> Store Γ
update here (S , x) v      = S , v
update (there p) (S , x) v = (update p S v) , x

decontextualize : ∀ {Γ}{n : Γ ⊢ `N} -> Storable n -> Val `N
decontextualize st-Z     = v-Z
decontextualize (st-S n) = v-S (decontextualize n)

contextualize : Val `N -> (Γ : Ctx) -> Γ ⊢ `N
contextualize v-Z Γ     = `Z
contextualize (v-S v) Γ = `S contextualize v Γ

add : ∀ {Γ τ}{t : Γ ⊢ τ} -> Store Γ -> Storable t -> Store (Γ , τ)
add {Γ} {`N} Σ s             = Σ , (decontextualize s)
add {Γ} {τ `→ τ₁} Σ (st-λ t) = Σ , v-⟨ Σ , t ⟩

data ⟨_×_⟩ : ∀ {Γ τ} -> Store Γ -> Γ ⊢ τ -> Set where
 ⟪_×_⟫ : ∀ {Γ τ} -> (Σ : Store Γ) -> (T : Γ ⊢ τ) -> ⟨ Σ × T ⟩ 


data _⟶_ : ∀ {Γ Δ τ}{Σ : Store Γ}{Σ' : Store Δ}{T : Γ ⊢ τ}{T' : Δ ⊢ τ} -> ⟨ Σ × T ⟩ -> ⟨ Σ' × T' ⟩ -> Set where

  `S-step : ∀ {Γ}{Σ Σ' : Store Γ}{n n' : Γ ⊢ `N}
    -> ⟪ Σ × n ⟫ ⟶ ⟪ Σ' × n' ⟫
    ----------------------------------
    -> ⟪ Σ × `S n ⟫ ⟶ ⟪ Σ' × `S n' ⟫

  `let-step : ∀ {Γ τ}{Σ Σ' : Store Γ}{n n' : Γ ⊢ `N}{T : Γ , `N ⊢ τ}
    -> ⟪ Σ × n ⟫ ⟶ ⟪ Σ' × n' ⟫
    --------------------------------------------------
    -> ⟪ Σ × `let n `in T ⟫ ⟶ ⟪ Σ' × `let n' `in T ⟫

  `let-store :
    ∀ {Γ τ}{Σ : Store Γ}{n : Γ ⊢ `N}{T : Γ , `N ⊢ τ}
    -> (s : Storable n)
    -----------------------------------------------------------
    -> ⟪ Σ × `let n `in T ⟫ ⟶ ⟪ Σ , decontextualize s × T ⟫

  `$-anon :
    ∀ {Γ τ σ}{Σ : Store Γ}{b : Γ , τ ⊢ σ}{t : Γ ⊢ τ}
    -> (s : Storable t)
    ------------------------------------------
    -> ⟪ Σ × (`λ b) `$ t ⟫ ⟶ ⟪ add Σ s × b ⟫

