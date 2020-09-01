```agda

module PCF+Stat.Dynamic where

open import PCF+Stat.Static

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

toVal : ∀ {Γ τ}{T : Γ ⊢ τ} -> Store Γ -> Storable T -> Val τ
toVal Σ st-Z     = v-Z
toVal Σ (st-S s) = v-S (toVal Σ s)
toVal Σ (st-λ t) = v-⟨ Σ , t ⟩

_!_ : ∀ {Γ τ} -> Γ ∋ τ -> Store Γ -> Val τ
here ! (_ , v)    = v
there p ! (Σ , _) = p ! Σ

update : ∀ {Γ τ} -> Γ ∋ τ -> Store Γ -> Val τ -> Store Γ
update here (S , x) v      = S , v
update (there p) (S , x) v = (update p S v) , x

{--
decontextualize : ∀ {Γ}{n : Γ ⊢ `N} -> Storable n -> Val `N
decontextualize st-Z     = v-Z
decontextualize (st-S n) = v-S (decontextualize n)

contextualize : Val `N -> (Γ : Ctx) -> Γ ⊢ `N
contextualize v-Z Γ     = `Z
contextualize (v-S v) Γ = `S contextualize v Γ

add : ∀ {Γ τ}{t : Γ ⊢ τ} -> Store Γ -> Storable t -> Store (Γ , τ)
add {Γ} {`N} Σ s             = Σ , (decontextualize s)
add {Γ} {τ `→ τ₁} Σ (st-λ t) = Σ , v-⟨ Σ , t ⟩
-}

data ⟨_×_⟩ : ∀ {Γ τ} -> Store Γ -> Γ ⊢ τ -> Set where
 ⟪_×_⟫ : ∀ {Γ τ} -> (Σ : Store Γ) -> (T : Γ ⊢ τ) -> ⟨ Σ × T ⟩ 


data _⟶_ : ∀ {Γ Δ τ}{Σ : Store Γ}{Σ' : Store Δ}{T : Γ ⊢ τ}{T' : Δ ⊢ τ} -> ⟨ Σ × T ⟩ -> ⟨ Σ' × T' ⟩ -> Set where

  `S-step : ∀ {Γ}{Σ Σ' : Store Γ}{n n' : Γ ⊢ `N}
    -> ⟪ Σ × n ⟫ ⟶ ⟪ Σ' × n' ⟫
    ----------------------------------
    -> ⟪ Σ × `S n ⟫ ⟶ ⟪ Σ' × `S n' ⟫

  `let-step : ∀ {Γ τ σ}{Σ Σ' : Store Γ}{t t' : Γ ⊢ τ}{T : Γ , τ ⊢ σ}
    -> ⟪ Σ × t ⟫ ⟶ ⟪ Σ' × t' ⟫
    --------------------------------------------------
    -> ⟪ Σ × `let t `in T ⟫ ⟶ ⟪ Σ' × `let t' `in T ⟫

  `let-store :
    ∀ {Γ τ σ}{Σ : Store Γ}{v : Γ ⊢ σ}{T : Γ , σ ⊢ τ}
    -> (s : Storable v)
    -------------------------------------------------
    -> ⟪ Σ × `let v `in T ⟫ ⟶ ⟪ Σ , toVal Σ s × T ⟫

  `$-anon :
    ∀ {Γ τ σ}{Σ : Store Γ}{b : Γ , τ ⊢ σ}{t : Γ ⊢ τ}
    -> (s : Storable t)
    -----------------------------------------------
    -> ⟪ Σ × (`λ b) `$ t ⟫ ⟶ ⟪ Σ , toVal Σ s × b ⟫

  `$-closure :
    ∀ {Γ τ σ}{Σ : Store Γ}{db : Γ ∋ τ `→ σ}{t : Γ ⊢ τ}
    -> (s : Storable t)
    -----------------------------------------------------------------------------------
    -> ⟪ Σ × (`! db) `$ t ⟫ ⟶ ⟪ (getStore (db ! Σ)) , (toVal Σ s) × getBody (db ! Σ) ⟫


```
