```agda

module PCF+While.Dynamic where

open import PCF+While.Static

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

    v-μ :
      ∀ {Γ τ}
      -> Store Γ
      -> Γ , τ ⊢ τ
      -> Val τ

  data Store : Ctx -> Set where
    ∅   : Store ∅
    _,_ : ∀ {Γ τ} -> Store Γ -> Val τ -> Store (Γ , τ)

getCtx : ∀ {τ σ} ->  Val (τ `→ σ) -> Ctx
getCtx (v-⟨_,_⟩ {Γ} _ _) = Γ
getCtx (v-μ {Γ} _ _)     = Γ

getStore : ∀ {τ σ} -> (v : Val (τ `→ σ)) -> Store (getCtx v)
getStore v-⟨ Σ , _ ⟩ = Σ
getStore (v-μ Σ _)   = Σ

getBody : ∀ {τ σ} -> (v : Val (τ `→ σ)) -> (getCtx v) , τ ⊢ σ
getBody v-⟨ _ , b ⟩ = b
getBody (v-μ _ b)   = `μ (`! here)

data Storable : ∀ {Γ τ} -> Γ ⊢ τ -> Set where
  st-Z : ∀ {Γ} -> Storable (`Z {Γ})
  st-S : ∀ {Γ}{n : Γ ⊢ `N} -> Storable n -> Storable (`S n)
  st-λ : ∀ {Γ τ σ} -> (t : Γ , τ ⊢ σ) -> Storable (`λ t)
  st-μ : ∀ {Γ τ} -> (t : Γ , τ ⊢ τ) -> Storable (`μ t)

toVal : ∀ {Γ τ}{T : Γ ⊢ τ} -> Store Γ -> Storable T -> Val τ
toVal Σ st-Z     = v-Z
toVal Σ (st-S s) = v-S (toVal Σ s)
toVal Σ (st-λ t) = v-⟨ Σ , t ⟩
toVal Σ (st-μ t) = v-μ Σ t

contextualize : Val `N -> (Γ : Ctx) -> Γ ⊢ `N
contextualize v-Z Γ       = `Z
contextualize (v-S v) Γ   = `S contextualize v Γ
contextualize (v-μ Σ b) Γ = `Z

_!_ : ∀ {Γ τ} -> Γ ∋ τ -> Store Γ -> Val τ
here ! (_ , v)    = v
there p ! (Σ , _) = p ! Σ

update : ∀ {Γ τ} -> Γ ∋ τ -> Store Γ -> Val τ -> Store Γ
update here (S , x) v      = S , v
update (there p) (S , x) v = (update p S v) , x

data ⟨_×_⟩ : ∀ {Γ τ} -> Store Γ -> Γ ⊢ τ -> Set where
 ⟪_×_⟫ : ∀ {Γ τ} -> (Σ : Store Γ) -> (T : Γ ⊢ τ) -> ⟨ Σ × T ⟩ 

mutual
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

    `!-nat :
      ∀ {Γ}{Σ : Store Γ}{db : Γ ∋ `N}
      -----------------------------------------------------
      -> ⟪ Σ × `! db ⟫ ⟶ ⟪ Σ × contextualize (db ! Σ) Γ ⟫

    `$-closure :
      ∀ {Γ τ σ}{Σ : Store Γ}{db : Γ ∋ τ `→ σ}{t : Γ ⊢ τ}
      -> (s : Storable t)
      -----------------------------------------------------------------------------------
      -> ⟪ Σ × (`! db) `$ t ⟫ ⟶ ⟪ (getStore (db ! Σ)) , (toVal Σ s) × getBody (db ! Σ) ⟫
    
    `$-anon :
      ∀ {Γ τ σ}{Σ : Store Γ}{b : Γ , τ ⊢ σ}{t : Γ ⊢ τ}
      -> (s : Storable t)
      -----------------------------------------------
      -> ⟪ Σ × (`λ b) `$ t ⟫ ⟶ ⟪ Σ , toVal Σ s × b ⟫

    `$-step :
      ∀ {Γ τ σ}{Σ Σ' : Store Γ}{F : Γ ⊢ τ `→ σ}{A A' : Γ ⊢ τ}
      -> ⟪ Σ × A ⟫ ⟶ ⟪ Σ' × A' ⟫
      -------------------------------------
      -> ⟪ Σ × F `$ A ⟫ ⟶ ⟪ Σ' × F `$ A' ⟫

    `<-step :
      ∀ {Γ τ}{Σ Σ' : Store Γ}{db : Γ ∋ τ}{v v' : Γ ⊢ τ}
      -> ⟪ Σ × v ⟫ ⟶ ⟪ Σ' × v' ⟫
      ----------------------------------------
      -> ⟪ Σ × db `← v ⟫ ⟶ ⟪ Σ' × db `← v' ⟫

    `<-done :
      ∀ {Γ τ}{Σ Σ' : Store Γ}{db : Γ ∋ τ}{v : Γ ⊢ τ}
      -> (s : Storable v)
      ----------------------------------------------------------
      -> ⟪ Σ × db `← v ⟫ ⟶ ⟪ update db Σ (toVal Σ s) × `done ⟫

    `,-step :
      ∀ {Γ τ}{Σ Σ' : Store Γ}{s s' : Γ ⊢ `1}{T : Γ ⊢ τ}
      -> ⟪ Σ × s ⟫ ⟶ ⟪ Σ' × s' ⟫
      --------------------------------------
      -> ⟪ Σ × s `, T ⟫ ⟶ ⟪ Σ' × s' `, T ⟫

    `,-done :
      ∀ {Γ τ}{Σ : Store Γ}{T : Γ ⊢ τ}
      -----------------------------------
      -> ⟪ Σ × `done `, T ⟫ ⟶ ⟪ Σ × T ⟫

    `case-step :
      ∀ {Γ τ}{Σ Σ' : Store Γ}{n n' : Γ ⊢ `N}{a : Γ ⊢ τ}{b : Γ ⊢ `N `→ τ}
      -> ⟪ Σ × n ⟫ ⟶ ⟪ Σ' × n' ⟫
      ---------------------------------------------------------------
      -> ⟪ Σ × `case n [Z a |S b ] ⟫ ⟶ ⟪ Σ' × `case n' [Z a |S b ] ⟫

    `case-zero :
      ∀ {Γ τ}{Σ : Store Γ}{a : Γ ⊢ τ}{b : Γ ⊢ `N `→ τ}
      ------------------------------------------------
      -> ⟪ Σ × `case `Z [Z a |S b ] ⟫ ⟶ ⟪ Σ × a ⟫

    `case-suc :
      ∀ {Γ τ}{Σ : Store Γ}{n : Γ ⊢ `N}{a : Γ ⊢ τ}{f : Γ ⊢ `N `→ τ}
--    -> Storable n -- no need, just weak head normal form ?
      ----------------------------------------------------
      -> ⟪ Σ × `case `S n [Z a |S f ] ⟫ ⟶ ⟪ Σ × f `$ n ⟫

    `while-step :
      ∀ {Γ}{Σ Σ' : Store Γ}{c c' : Γ ⊢ `N}{T : Γ ⊢ `1}
      -> ⟪ Σ × c ⟫ ⟶ ⟪ Σ' × c' ⟫
      ------------------------------------------------------
      -> ⟪ Σ × `while c `do T ⟫ ⟶ ⟪ Σ' × `while c' `do T ⟫

    `while-Z :
      ∀ {Γ}{Σ Σ' : Store Γ}{c : Γ ⊢ `N}{T : Γ ⊢ `1}
      -> ⟪ Σ × c ⟫ ==> ⟪ Σ' × `Z ⟫
      -------------------------------------------
      -> ⟪ Σ × `while `Z `do T ⟫ ⟶ ⟪ Σ × `done ⟫


    `while-S :
      ∀ {Γ}{Σ Σ' : Store Γ}{c c' : Γ ⊢ `N}{T : Γ ⊢ `1}
      -> ⟪ Σ × c ⟫ ==> ⟪ Σ' × `S c' ⟫
      ------------------------------------------------------------
      -> ⟪ Σ × `while c `do T ⟫ ⟶ ⟪ Σ' × T `, (`while c `do T) ⟫  


    `μ-reduc :
      ∀ {Γ τ}{Σ : Store Γ}{T : Γ , τ ⊢ τ}
      -> (s : Storable (`μ T))
      -----------------------------------------
      -> ⟪ Σ × `μ T ⟫ ⟶ ⟪ Σ , toVal Σ s × T ⟫

  data _==>_ : ∀ {Γ Δ τ}{Σ : Store Γ}{Σ' : Store Δ}{T : Γ ⊢ τ}{T' : Δ ⊢ τ}
               -> ⟨ Σ × T ⟩ -> ⟨ Σ' × T' ⟩ -> Set where

    _■ : ∀ {Γ τ}{Σ : Store Γ}
      -> (T : Γ ⊢ τ)
      --------------------------
      -> ⟪ Σ × T ⟫ ==> ⟪ Σ × T ⟫

    _⟶⟨_⟩_ : ∀ {Γ₁ Γ₂ Γ₃ τ}{Σ₁ : Store Γ₁}{Σ₂ : Store Γ₂}{Σ₃ : Store Γ₃}
             (T₁ : Γ₁ ⊢ τ){T₂ : Γ₂ ⊢ τ}{T₃ : Γ₃ ⊢ τ}
             -> ⟪ Σ₁ × T₁ ⟫ ⟶ ⟪ Σ₂ × T₂ ⟫
             -> ⟪ Σ₂ × T₂ ⟫ ==> ⟪ Σ₃ × T₃ ⟫
             -------------------------------
             -> ⟪ Σ₁ × T₁ ⟫ ==> ⟪ Σ₃ × T₃ ⟫


```
