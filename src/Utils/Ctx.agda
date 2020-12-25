module Utils.Ctx (Ty : Set) where

open import Relation.Binary.PropositionalEquality

infix 8 _⊑_
infixl 10 _,_

data Ctx : Set where
  ∅ : Ctx
  _,_ : Ctx -> Ty -> Ctx

private
  variable
    Γ Δ Φ : Ctx
    τ σ φ : Ty
    P Q   : Ty -> Set
    
data _⊑_ : Ctx -> Ctx -> Set where
  ∅-⊑ : ∅ ⊑ Γ
  ,-⊑ : Γ ⊑ Δ -> τ ≡ σ -> Γ , τ ⊑ Δ , σ

_ : ∅ , τ , σ  ⊑ ∅ , φ , τ , σ 
_ = ,-⊑ (,-⊑ ∅-⊑ refl) refl

_⨀_ : Γ ⊑ Δ -> Δ ⊑ Φ -> Γ ⊑ Φ
∅-⊑        ⨀ _                                  = ∅-⊑
,-⊑ pr1 eq ⨀ ,-⊑ pr2 eq₁ rewrite eq rewrite eq₁ = ,-⊑ (pr1 ⨀ pr2) refl

data Any (P : Ty -> Set) : Ctx -> Set where
  here  : P τ -> (Γ : Ctx) -> Any P (Γ , τ)
  there : Any P Γ -> Any P (Γ , τ)

_∋_ : Ctx -> Ty -> Set
Γ ∋ τ = Any (λ x -> x ≡ τ) Γ

-- Once Value depending at least on Ty is defined, a store is All (λ t -> Value t) Γ
data All (P : Ty -> Set) : Ctx -> Set where
  ∅   : All P ∅
  _,_ : All P Γ -> P τ -> All P (Γ , τ)

lookup : ∀ {P : Ty -> Set} -> All P Γ -> Γ ∋ τ -> P τ
lookup (_   , x) (here x₁ _) rewrite x₁ = x
lookup (all , _) (there p) = lookup all p

update : All P Γ -> Γ ∋ τ -> P τ -> All P Γ
update (all , Pσ) (here τ≡σ Γ) Pτ rewrite τ≡σ = all , Pτ
update (all , Pσ) (there Γ∋τ) Pτ              = update all Γ∋τ Pτ , Pσ

convert : (f : ∀ {τ} -> P τ -> Q τ) -> All P Γ -> All Q Γ
convert f ∅         = ∅
convert f (all , x) = convert f all , f x


  

    
