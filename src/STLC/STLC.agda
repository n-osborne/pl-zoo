module STLC.STLC where

infixr 9 _,_
infixr 7 _⇒_
infixl 6 _`$_
infix  5 _∋_ _⊢_ _⟶_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty -> Ty -> Ty

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Ty -> Ctx

data _∋_ : Ctx -> Ty -> Set where
  here : ∀ {Γ τ} -> Γ , τ ∋ τ
  there : ∀ {Γ τ σ} -> Γ ∋ τ -> Γ , σ ∋ τ

data _⊢_ : Ctx -> Ty -> Set where
  `V_ : ∀ {Γ τ}
    -> Γ ∋ τ
    --------
    -> Γ ⊢ τ

  `λ_ : ∀ {Γ τ σ}
    -> Γ , τ ⊢ σ
    ------------
    -> Γ ⊢ τ ⇒ σ

  _`$_ : ∀ {Γ τ σ}
    -> Γ ⊢ τ ⇒ σ
    -> Γ ⊢ τ
    ------------
    -> Γ ⊢ σ

record Kit (_◆_ : Ctx -> Ty -> Set) : Set where
  constructor kit
  field
    vr : ∀ {Γ τ} -> Γ ∋ τ -> Γ ◆ τ
    tm : ∀ {Γ τ} -> Γ ◆ τ -> Γ ⊢ τ
    wk : ∀ {Γ τ σ} -> Γ ◆ τ -> (Γ , σ) ◆ τ

lift : ∀ {Γ Δ τ σ}{_◆_ : Ctx -> Ty -> Set} -> Kit _◆_ -> (∀ {X} -> Γ ∋ X -> Δ ◆ X) -> Γ , σ ∋ τ -> (Δ , σ) ◆ τ
lift (kit vr tm wk) μ here = vr here
lift (kit vr tm wk) μ (there p) = wk (μ p)

trav : ∀ {Γ Δ τ}{_◆_ : Ctx -> Ty -> Set} -> Kit _◆_ -> (∀ {X} -> Γ ∋ X -> Δ ◆ X) -> Γ ⊢ τ -> Δ ⊢ τ
trav (kit vr tm wk) μ (`V x) = tm (μ x)
trav K μ (`λ t)              = `λ trav K (lift K μ) t
trav K μ (t `$ t₁)           = trav K μ t `$ trav K μ t₁

rename : ∀ {Γ Δ τ} -> (∀ {X} -> Γ ∋ X -> Δ ∋ X) -> Γ ⊢ τ -> Δ ⊢ τ
rename ρ t = trav (kit (λ x -> x) `V_ there) ρ t

subst : ∀ {Γ Δ τ} -> (∀ {X} -> Γ ∋ X -> Δ ⊢ X) -> Γ ⊢ τ -> Δ ⊢ τ
subst σ t = trav (kit `V_ (λ x -> x) (rename there)) σ t

_[_] : ∀ {Γ τ σ} -> Γ , σ ⊢ τ -> Γ ⊢ σ -> Γ ⊢ τ
_[_] {Γ}{τ}{σ} F A = subst {Γ , σ}{Γ}{τ} μ F
  where
    μ : ∀ {φ} -> Γ , σ ∋ φ -> Γ ⊢ φ
    μ here      = A
    μ (there p) = `V p

data Value : ∀ {Γ τ} -> Γ ⊢ τ -> Set where
  val`λ : ∀ {Γ τ σ}{N : Γ , τ ⊢ σ} -> Value (`λ N)
  
data _⟶_ : ∀ {Γ τ} -> Γ ⊢ τ -> Γ ⊢ τ -> Set where

  `$-right : ∀ {Γ τ σ}{F : Γ ⊢ τ ⇒ σ}{A A' : Γ ⊢ τ}
    -> Value F
    -> A ⟶ A'
    ---------------------
    -> F `$ A ⟶ F `$ A'

  `$-left : ∀ {Γ τ σ}{F F' : Γ ⊢ τ ⇒ σ}{A : Γ ⊢ τ}
    -> F ⟶ F'
    ---------------------
    -> F `$ A ⟶ F' `$ A

  `$-subst : ∀ {Γ τ σ}{B : Γ , τ ⊢ σ}{A : Γ ⊢ τ}
    -> Value A
    -----------------------
    -> `λ B `$ A ⟶ B [ A ]

data _⟶*_ : ∀ {Γ τ} -> Γ ⊢ τ -> Γ ⊢ τ -> Set where

  red-refl : ∀ {Γ τ}{T : Γ ⊢ τ}
    -> T ⟶* T

  red-trans : ∀ {Γ τ}{T₀ T₁ T₂ : Γ ⊢ τ}
    -> T₀ ⟶ T₁
    -> T₁ ⟶* T₂
    -------------
    -> T₀ ⟶* T₂

data Progress {τ}(M : ε ⊢ τ) : Set where

  step : ∀ {N : ε ⊢ τ}
    -> M ⟶ N
    -------------
    -> Progress M

  done :
    Value M
    -------------
    -> Progress M

progress : ∀ {τ} -> (M : ε ⊢ τ) -> Progress M
progress (`λ m) = done val`λ
progress (m `$ m₁) with progress m
progress (m `$ m₁)       | step x = step (`$-left x)
progress (m `$ m₁)       | done x with progress m₁
progress (m `$ m₁)       | done x     | step x₁ = step (`$-right x x₁)
progress (.(`λ _) `$ m₁) | done val`λ | done x₁ = step (`$-subst x₁)
