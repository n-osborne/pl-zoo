module WhileRec.Ty where

open import Data.Product using (_×_; uncurry) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂)
open import Relation.Nullary.Product     using (_×-dec_)
open import Relation.Nullary             using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable   using (map′)

infixr 5 _`⇒_

data Ty : Set where
  `1 `N : Ty
  `ref  : Ty -> Ty
  _`⇒_ : Ty -> Ty -> Ty

`ref-injective : forall {τ τ₁} -> (`ref τ) ≡ (`ref τ₁) -> (τ ≡ τ₁)
`ref-injective refl = refl
    
`ref-dec : forall {τ τ₁} -> Dec (τ ≡ τ₁) -> Dec (`ref τ ≡ `ref τ₁)
`ref-dec τ≡τ₁ = map′ (cong `ref) `ref-injective τ≡τ₁

`⇒-injective : forall {τ τ₁ τ₂ τ₃} -> (τ `⇒ τ₁) ≡ (τ₂ `⇒ τ₃) -> (τ ≡ τ₂) × (τ₁ ≡ τ₃)
`⇒-injective refl = ⟨ refl , refl ⟩
  
`⇒-dec : forall {τ τ₁ τ₂ τ₃} -> Dec (τ ≡ τ₁) -> Dec (τ₂ ≡ τ₃) -> Dec (τ `⇒ τ₂ ≡ τ₁ `⇒ τ₃)
`⇒-dec τ≡τ₁ τ₂≡τ₃ = map′ (uncurry (cong₂ _`⇒_)) `⇒-injective (τ≡τ₁ ×-dec τ₂≡τ₃)

_≟_ : (τ : Ty) -> (σ : Ty) -> Dec (τ ≡ σ)
`1        ≟ `1        = yes refl
`1        ≟ `N        = no (λ ())
`1        ≟ `ref σ    = no (λ ())
`1        ≟ (σ `⇒ σ₁) = no (λ ())
`N        ≟ `1        = no (λ ())
`N        ≟ `N        = yes refl
`N        ≟ `ref σ    = no (λ ())
`N        ≟ (σ `⇒ σ₁) = no (λ ())
`ref τ    ≟ `1        = no (λ ())
`ref τ    ≟ `N        = no (λ ())
`ref τ    ≟ `ref σ    = `ref-dec (τ ≟ σ)
`ref τ    ≟ (σ `⇒ σ₁) = no (λ ())
(τ `⇒ τ₁) ≟ `1        = no (λ ())
(τ `⇒ τ₁) ≟ `N        = no (λ ())
(τ `⇒ τ₁) ≟ `ref σ    = no (λ ())
(τ `⇒ τ₁) ≟ (σ `⇒ σ₁) = `⇒-dec (τ ≟ σ) (τ₁ ≟ σ₁)
