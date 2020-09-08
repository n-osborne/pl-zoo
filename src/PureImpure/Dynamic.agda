module PureImpure.Dynamic where

open import PureImpure.Static

mutual
  data Val : PreTy -> Set where

    v-Z : Val `N
    v-S : Val `N -> Val `N
    v-λ : ∀ {φ : Ty σ} -> Store Γ -> Γ , τ ⊢ φ -> Val (τ `→ σ)

  data Store : Ctx -> Set where
    ∅   : Store ∅
    _,_ : Store Γ -> Val τ -> Store (Γ , τ)

data Storable : Γ ⊢ `pure τ -> Set where
  st-Z : Storable (`Z {Γ})
  st-S : {n : Γ ⊢ `pure `N} -> Storable n -> Storable (`S n)
  st-λ : {φ : Ty σ} -> (b : Γ , τ ⊢ φ) -> Storable (`λ b)
  
toVal : {T : Γ ⊢ `pure τ} -> Store Γ -> Storable T -> Val τ
toVal Σ st-Z     = v-Z
toVal Σ (st-S n) = v-S (toVal Σ n)
toVal Σ (st-λ b) = v-λ Σ b

_!_ : Γ ∋ τ -> Store Γ -> Val τ
here ! (_ , v)     = v
there db ! (Σ , _) = db ! Σ

update : Store Γ ->  Γ ∋ τ -> Val τ -> Store Γ
update (Σ , _) here v       = Σ , v
update (Σ , x) (there db) v = (update Σ db v) , x

contextualize : Val `N -> (Γ : Ctx) -> Γ ⊢ `pure `N
contextualize v-Z Γ     = `Z
contextualize (v-S v) Γ = `S (contextualize v Γ)

getCtx : Val (τ `→ σ) -> Ctx
getCtx (v-λ {Γ = Γ} _ _) = Γ

getStore : (v : Val (τ `→ σ)) -> Store (getCtx v)
getStore (v-λ Σ _) = Σ

getBody : ∀ {φ : Ty σ} -> (v : Val (τ `→ σ)) -> getCtx v , τ ⊢ φ
getBody (v-λ _ b) = {!!}

data ⟪_×_⟫ : ∀ {φ : Ty τ} -> Store Γ -> Γ ⊢ φ -> Set where
  ⟨_×_⟩ : ∀ {φ : Ty τ}(Σ : Store Γ) -> (T : Γ ⊢ φ) -> ⟪ Σ × T ⟫

data Done : Γ ⊢ `impure τ -> Set where

purify : {T : Γ ⊢ `impure τ} -> Done T -> Γ ⊢ `pure τ
purify d = {!!}

data _⟶_ : ∀ {φ ψ : Ty τ}{Σ : Store Γ}{Σ' : Store Δ}{T : Γ ⊢ φ}{T' : Δ ⊢ ψ}
             -> ⟪ Σ × T ⟫ -> ⟪ Σ' × T' ⟫ -> Set where

     S-step :
       ∀ {Σ : Store Γ}{N N' : Γ ⊢ `pure `N}
       -> ⟨ Σ × N ⟩ ⟶ ⟨ Σ × N' ⟩
       --------------------------------
       -> ⟨ Σ × `S N ⟩ ⟶ ⟨ Σ × `S N' ⟩

     case-step :
       ∀ {φ : Ty τ}{Σ : Store Γ}{N N' : Γ ⊢ `pure `N}{T₀ : Γ ⊢ φ}{T₁ : Γ , `N ⊢ φ}
       -> ⟨ Σ × N ⟩ ⟶ ⟨ Σ × N' ⟩
       --------------------------------------------------------------------
       -> ⟨ Σ × `case N [Z T₀ |S T₁ ] ⟩ ⟶ ⟨ Σ × `case N' [Z T₀ |S T₁ ] ⟩

     case-zero :
       ∀ {φ : Ty τ}{Σ : Store Γ}{T₀ : Γ ⊢ φ}{T₁ : Γ , `N ⊢ φ}
       --------------------------------------------------------------
       -> ⟨ Σ × `case `Z [Z T₀ |S T₁ ] ⟩ ⟶ ⟨ Σ × T₀ ⟩

     case-succ :
       ∀ {φ : Ty τ}{Σ : Store Γ}{T₀ : Γ ⊢ φ}{T₁ : Γ , `N ⊢ φ}{n : Γ ⊢ `pure `N}
       -> (s : Storable n)
       --------------------------------------------------------------
       -> ⟨ Σ × `case `S n [Z T₀ |S T₁ ] ⟩ ⟶ ⟨ Σ , toVal Σ s × T₁ ⟩
     
     if-step :
       ∀ {φ : Ty τ}{Σ : Store Γ}{N N' : Γ ⊢ `pure `N}{T₀ T₁ : Γ ⊢ φ}
       -> ⟨ Σ × N ⟩ ⟶ ⟨ Σ × N' ⟩
       --------------------------------------------------------------------
       -> ⟨ Σ × `if N `then T₀ `else T₁ ⟩ ⟶ ⟨ Σ × `if N' `then T₀ `else T₁ ⟩

     if-zero :
       ∀ {φ : Ty τ}{Σ : Store Γ}{T₀ T₁ : Γ ⊢ φ}
       ---------------------------------------------------
       -> ⟨ Σ × `if `Z `then T₀ `else T₁ ⟩ ⟶ ⟨ Σ × T₀ ⟩

     if-succ :
       ∀ {φ : Ty τ}{Σ : Store Γ}{T₀ T₁ : Γ ⊢ φ}{n : Γ ⊢ `pure `N}
       ----------------------------------------------------------
       -> ⟨ Σ × `if `S n `then T₀ `else T₁ ⟩ ⟶ ⟨ Σ × T₁ ⟩

     ret-step :
       ∀ {Σ Σ' : Store Γ}{T T' : Γ ⊢ `impure τ}
       -> ⟨ Σ × T ⟩ ⟶ ⟨ Σ' × T' ⟩
       -----------------------------------
       -> ⟨ Σ × `ret T ⟩ ⟶ ⟨ Σ' × `ret T' ⟩

     ret-done :
       ∀ {Σ : Store Γ}{T : Γ ⊢ `impure τ}
       -> (D : Done T)
       -----------------------------------
       -> ⟨ Σ × `ret T ⟩ ⟶ ⟨ Σ × purify D ⟩
     $-step :
       ∀ {φ : Ty σ}{Σ : Store Γ}{F : Γ , τ ⊢ φ}{A A' : Γ ⊢ `pure τ}
       -> ⟨ Σ × A ⟩ ⟶ ⟨ Σ × A' ⟩
       ------------------------------------------
       -> ⟨ Σ × `λ F `$ A ⟩ ⟶ ⟨ Σ × `λ F `$ A' ⟩

     $-app :
       ∀ {φ : Ty σ}{Σ : Store Γ}{F : Γ , τ ⊢ φ}{A : Γ ⊢ `pure τ}
       -> (S : Storable A)
       ---------------------------------------------
       -> ⟨ Σ × `λ F `$ A ⟩ ⟶ ⟨ Σ , toVal Σ S × F ⟩

     $$-step :
       ∀ {Σ : Store Γ}{F : Γ ∋ (τ `→ σ)}{A A' : Γ ⊢ `pure τ}
       -> ⟨ Σ × A ⟩ ⟶ ⟨ Σ × A' ⟩
       ----------------------------------------
       -> ⟨ Σ × F `$$ A ⟩ ⟶ ⟨ Σ × F `$$ A' ⟩

     $$-app :
       ∀ {Σ : Store Γ}{F : Γ ∋ (τ `→ σ)}{A : Γ ⊢ `pure τ}
       -> (S : Storable A)
       ---------------------------------------------------------------------------------
       -> ⟨ Σ × F `$$ A ⟩ ⟶ ⟨ getStore (F ! Σ) , (toVal Σ S) × `ret (getBody (F ! Σ)) ⟩

     let-step :
       ∀ {Σ : Store Γ}{E E' : Γ ⊢ `pure τ}{φ : Ty σ}{T : Γ , τ ⊢ φ}
       -> ⟨ Σ × E ⟩ ⟶ ⟨ Σ × E' ⟩
       -------------------------------------------------
       -> ⟨ Σ × `let E `in T ⟩ ⟶ ⟨ Σ × `let E' `in T ⟩

     let-reduc :
       ∀ {Σ : Store Γ}{E : Γ ⊢ `pure τ}{φ : Ty σ}{T : Γ , τ ⊢ φ}
       -> (S : Storable E)
       -------------------------------------------------
       -> ⟨ Σ × `let E `in T ⟩ ⟶ ⟨ Σ , toVal Σ S × T ⟩

     <-step :
       ∀ {Σ : Store Γ}{db : Γ ∋ τ}{E E' : Γ ⊢ `pure τ}
       -> ⟨ Σ × E ⟩ ⟶ ⟨ Σ × E' ⟩
       ---------------------------------------
       -> ⟨ Σ × db `← E ⟩ ⟶ ⟨ Σ × db `← E' ⟩

     <-reduc :
       ∀ {Σ : Store Γ}{db : Γ ∋ τ}{E : Γ ⊢ `pure τ}
       -> (S : Storable E)
       ----------------------------------------------------------
       -> ⟨ Σ × db `← E ⟩ ⟶ ⟨ update Σ db (toVal Σ S) × `done ⟩

     while-rewrite :
       ∀ {Σ : Store Γ}{n : Γ ⊢ `pure `N}{T : Γ ⊢ `impure `1}
       --------------------------------------------------------------------------------
       -> ⟨ Σ × `while n `do T ⟩ ⟶ ⟨ Σ × `if n `then T `else (T `, (`while n `do T)) ⟩

     seq-step :
       ∀ {Σ Σ' : Store Γ}{T₀ T₀' : Γ ⊢ `impure `1}{φ : Ty τ}{T₁ : Γ  ⊢ φ}
       -> ⟨ Σ × T₀ ⟩ ⟶ ⟨ Σ' × T₀' ⟩
       -----------------------------------------
       -> ⟨ Σ × T₀ `, T₁ ⟩ ⟶ ⟨ Σ' × T₀' `, T₁ ⟩

     seq-done :
       ∀ {Σ : Store Γ}{φ : Ty τ}{T : Γ ⊢ φ}
       -------------------------------------
       -> ⟨ Σ × `done `, T ⟩ ⟶ ⟨ Σ × T ⟩

     !-get :
       ∀ {Σ : Store Γ}{db : Γ ∋ `N}
       ----------------------------------------------------
       -> ⟨ Σ × `! db ⟩ ⟶ ⟨ Σ × contextualize (db ! Σ) Γ ⟩
