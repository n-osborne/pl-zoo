```agda
module PureImpure.Dynamic where

open import PureImpure.Static

mutual
  data Val : Ty -> Set where
    v-Z : Val `N
    v-S : Val `N -> Val `N
    v-λ : Store Γ -> [ ζ ] Γ , τ ⊢ σ -> Val (τ `→ σ)

  data Store : Ctx -> Set where
    ∅   : Store ∅
    _,_ : Store Γ -> Val τ -> Store (Γ , τ)

data Storable : [ ζ ] Γ ⊢ τ -> Set where
  st-Z : Storable (`Z {Γ})
  st-S : {n : [ `pure ] Γ ⊢ `N} -> Storable n -> Storable (`S n)
  st-λ : (b : [ ζ ] Γ , τ ⊢ σ) -> Storable (`λ b)
  
toVal : {T : [ ζ ] Γ ⊢ τ} -> Store Γ -> Storable T -> Val τ
toVal Σ st-Z     = v-Z
toVal Σ (st-S n) = v-S (toVal Σ n)
toVal Σ (st-λ b) = v-λ Σ b

_!_ : Γ ∋ τ -> Store Γ -> Val τ
here ! (_ , v)     = v
there db ! (Σ , _) = db ! Σ

update : Store Γ ->  Γ ∋ τ -> Val τ -> Store Γ
update (Σ , _) here v       = Σ , v
update (Σ , x) (there db) v = (update Σ db v) , x

contextualize : Val `N -> (Γ : Ctx) -> [ `pure ] Γ ⊢ `N
contextualize v-Z Γ     = `Z
contextualize (v-S v) Γ = `S (contextualize v Γ)

getCtx : Val (τ `→ σ) -> Ctx
getCtx (v-λ {Γ = Γ} _ _) = Γ

getStore : (v : Val (τ `→ σ)) -> Store (getCtx v)
getStore (v-λ Σ _) = Σ

getBody : (v : Val (τ `→ σ)) -> [ `impure ] getCtx v , τ ⊢ σ
getBody (v-λ _ b) = `done `, b

data ⟪_×_⟫ : Store Γ -> [ ζ ] Γ ⊢ τ -> Set where
  ⟨_×_⟩ : (Σ : Store Γ) -> (T : [ ζ ] Γ ⊢ τ) -> ⟪ Σ × T ⟫

mutual
  data _⟶_ : ∀ {Σ : Store Γ}{Σ' : Store Δ}{T : [ ζ ] Γ ⊢ τ}{T' : [ ξ ] Δ ⊢ τ}
               -> ⟪ Σ × T ⟫ -> ⟪ Σ' × T' ⟫ -> Set where

       S-step :
         ∀ {Σ : Store Γ}{N N' : [ `pure ] Γ ⊢ `N}
         -> ⟨ Σ × N ⟩ ⟶ ⟨ Σ × N' ⟩
         --------------------------------
         -> ⟨ Σ × `S N ⟩ ⟶ ⟨ Σ × `S N' ⟩

       case-step :
         ∀ {Σ : Store Γ}{N N' : [ `pure ] Γ ⊢ `N}
           {T₀ : [ ζ ] Γ ⊢ τ}{T₁ : [ ζ ] Γ , `N ⊢ τ}
         -> ⟨ Σ × N ⟩ ⟶ ⟨ Σ × N' ⟩
         --------------------------------------------------------------------
         -> ⟨ Σ × `case N [Z T₀ |S T₁ ] ⟩ ⟶ ⟨ Σ × `case N' [Z T₀ |S T₁ ] ⟩

       case-zero :
         ∀ {Σ : Store Γ}{T₀ : [ ζ ] Γ ⊢ τ}{T₁ : [ ζ ] Γ , `N ⊢ τ}
         --------------------------------------------------------------
         -> ⟨ Σ × `case `Z [Z T₀ |S T₁ ] ⟩ ⟶ ⟨ Σ × T₀ ⟩

       case-succ :
         ∀ {Σ : Store Γ}{T₀ : [ ζ ] Γ ⊢ τ}{T₁ : [ ζ ] Γ , `N ⊢ τ}{n : [ `pure ] Γ ⊢ `N}
         -> (s : Storable n)
         --------------------------------------------------------------
         -> ⟨ Σ × `case `S n [Z T₀ |S T₁ ] ⟩ ⟶ ⟨ Σ , toVal Σ s × T₁ ⟩
     
       if-step :
         ∀ {Σ : Store Γ}{N N' : [ `pure ] Γ ⊢ `N}{T₀ T₁ : [ ζ ] Γ ⊢ τ}
         -> ⟨ Σ × N ⟩ ⟶ ⟨ Σ × N' ⟩
         --------------------------------------------------------------------
         -> ⟨ Σ × `if N `then T₀ `else T₁ ⟩ ⟶ ⟨ Σ × `if N' `then T₀ `else T₁ ⟩

       if-zero :
         ∀ {Σ : Store Γ}{T₀ T₁ : [ ζ ] Γ ⊢ τ}
         ---------------------------------------------------
         -> ⟨ Σ × `if `Z `then T₀ `else T₁ ⟩ ⟶ ⟨ Σ × T₀ ⟩

       if-succ :
         ∀ {Σ : Store Γ}{T₀ T₁ : [ ζ ] Γ ⊢ τ}{n : [ `pure ] Γ ⊢ `N}
         ----------------------------------------------------------
         -> ⟨ Σ × `if `S n `then T₀ `else T₁ ⟩ ⟶ ⟨ Σ × T₁ ⟩

       $-step :
         ∀ {Σ : Store Γ}{F : [ ζ ] Γ , τ ⊢ τ}{A A' : [ `pure ] Γ ⊢ τ}
         -> ⟨ Σ × A ⟩ ⟶ ⟨ Σ × A' ⟩
         ------------------------------------------
         -> ⟨ Σ × `λ F `$ A ⟩ ⟶ ⟨ Σ × `λ F `$ A' ⟩

       $-app :
         ∀ {Σ : Store Γ}{F : [ ζ ] Γ , τ ⊢ σ}{A : [ `pure ] Γ ⊢ τ}
         -> (S : Storable A)
         ---------------------------------------------
         -> ⟨ Σ × `λ F `$ A ⟩ ⟶ ⟨ Σ , toVal Σ S × F ⟩

       $!-step :
         ∀ {Σ : Store Γ}{F : Γ ∋ (τ `→ σ)}{A A' : [ `pure ] Γ ⊢ τ}
         -> ⟨ Σ × A ⟩ ⟶ ⟨ Σ × A' ⟩
         ----------------------------------------
         -> ⟨ Σ × F `$! A ⟩ ⟶ ⟨ Σ × F `$! A' ⟩

       $!-app :
         ∀ {Σ : Store Γ}{Σ' : Store Δ}{F : Γ ∋ (τ `→ σ)}{A : [ `pure ] Γ ⊢ τ}
           {T : [ `pure ] Δ ⊢ σ}
         -> (S : Storable A)
         -> ⟨ getStore (F ! Σ) , (toVal Σ S) × getBody (F ! Σ) ⟩ ⟶* ⟨ Σ' × T ⟩
         -> (S' : Storable T)
         --------------------------------------------------------------------------
         -> ⟨ Σ × F `$! A ⟩ ⟶ ⟨ Σ × T ⟩

       let-step :
         ∀ {Σ : Store Γ}{E E' : [ `pure ] Γ ⊢ τ}{T : [ ζ ] Γ , τ ⊢ σ}
         -> ⟨ Σ × E ⟩ ⟶ ⟨ Σ × E' ⟩
         -------------------------------------------------
         -> ⟨ Σ × `let E `in T ⟩ ⟶ ⟨ Σ × `let E' `in T ⟩

       let-reduc :
         ∀ {Σ : Store Γ}{E : [ `pure ] Γ ⊢ τ}{T : [ ζ ] Γ , τ ⊢ σ}
         -> (S : Storable E)
         -------------------------------------------------
         -> ⟨ Σ × `let E `in T ⟩ ⟶ ⟨ Σ , toVal Σ S × T ⟩

       <-step :
         ∀ {Σ : Store Γ}{db : Γ ∋ τ}{E E' : [ `pure ] Γ ⊢ τ}
         -> ⟨ Σ × E ⟩ ⟶ ⟨ Σ × E' ⟩
         ---------------------------------------
         -> ⟨ Σ × db `← E ⟩ ⟶ ⟨ Σ × db `← E' ⟩

       <-reduc :
         ∀ {Σ : Store Γ}{db : Γ ∋ τ}{E : [ `pure ] Γ ⊢ τ}
         -> (S : Storable E)
         ----------------------------------------------------------
         -> ⟨ Σ × db `← E ⟩ ⟶ ⟨ update Σ db (toVal Σ S) × `done ⟩

       while-rewrite :
         ∀ {Σ : Store Γ}{n : [ `pure ] Γ ⊢ `N}{T : [ `impure ] Γ ⊢ `1}
         --------------------------------------------------------------------------------
         -> ⟨ Σ × `while n `do T ⟩ ⟶ ⟨ Σ × `if n `then (T `, (`while n `do T)) `else `done ⟩

       seq-step :
         ∀ {Σ Σ' : Store Γ}{T₀ T₀' : [ `impure ] Γ ⊢ `1}{T₁ : [ ζ ] Γ  ⊢ σ}
         -> ⟨ Σ × T₀ ⟩ ⟶ ⟨ Σ' × T₀' ⟩
         -----------------------------------------
         -> ⟨ Σ × T₀ `, T₁ ⟩ ⟶ ⟨ Σ' × T₀' `, T₁ ⟩

       seq-done :
         ∀ {Σ : Store Γ}{T : [ ζ ] Γ ⊢ τ}
         -------------------------------------
         -> ⟨ Σ × `done `, T ⟩ ⟶ ⟨ Σ × T ⟩

       !-get :
         ∀ {Σ : Store Γ}{db : Γ ∋ `N}
         ----------------------------------------------------
         -> ⟨ Σ × `! db ⟩ ⟶ ⟨ Σ × contextualize (db ! Σ) Γ ⟩
```

Reflexive and transitive closure of reduction.

```
  data _⟶*_ : ∀ {Σ : Store Γ}{Σ' : Store Δ}{T : [ ζ ] Γ ⊢ τ}{T' : [ ξ ] Δ ⊢ τ}
               -> ⟪ Σ × T ⟫ -> ⟪ Σ' × T' ⟫ -> Set where

       *refl :
         ∀ {Σ : Store Γ}{T : [ ζ ] Γ ⊢ τ}
         ---------------------------------
         -> ⟨ Σ × T ⟩ ⟶* ⟨ Σ × T ⟩

       *trans :
         ∀ {Σ₀ : Store Γ}{Σ₁ : Store Δ}{Δ' : Ctx}{Σ₂ : Store Δ'}{δ : Status}
           {T₀ : [ ζ ] Γ ⊢ τ}{T₁ : [ ξ ] Δ ⊢ τ}{T₂ : [ δ ] Δ' ⊢ τ}
           -> ⟨ Σ₀ × T₀ ⟩ ⟶ ⟨ Σ₁ × T₁ ⟩
           -> ⟨ Σ₁ × T₁ ⟩ ⟶* ⟨ Σ₂ × T₂ ⟩
           -------------------------------
           -> ⟨ Σ₀ × T₀ ⟩ ⟶* ⟨ Σ₂ × T₂ ⟩
```
