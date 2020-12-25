module ParPCF.Dynamic where

open import ParPCF.Static

infix 5 _⟶_

postulate
  _[_] : ∀ {Γ τ σ} -> Γ , σ ⊢ τ -> Γ ⊢ σ -> Γ ⊢ τ
  
data Value : ∀ {Γ τ} -> Γ ⊢ τ -> Set where

  `Z-val : ∀ {Γ}
    -------------------
    -> Value {Γ}{`N} `Z

  `S-val : ∀ {Γ}{n : Γ ⊢ `N}
    -> Value n
    ---------------
    -> Value (`S n)

  `λ-val : ∀ {Γ τ σ}{T : Γ , σ ⊢ τ}
    --------------------------------
    -> Value (`λ T)

  `μ-val : ∀ {Γ τ}{T : Γ , τ ⊢ τ}
    -----------------------------
    -> Value (`μ T)

  `×-val : ∀ {Γ τ σ}{L : Γ ⊢ τ}{R : Γ ⊢ σ}
    -> Value L
    -> Value R
    -----------------
    -> Value (L `, R)

data _⟶_ : ∀ {Γ τ} -> Γ ⊢ τ -> Γ ⊢ τ -> Set where

  `N-step : ∀ {Γ}{N N' : Γ ⊢ `N}
    -> N ⟶ N'
    ----------------
    -> `S N ⟶ `S N'

  `$-step : ∀ {Γ τ σ}{F : Γ ⊢ σ `→ τ}{A A' : Γ ⊢ σ}
    -> A ⟶ A'
    --------------------------
    -> F `$ A ⟶ F `$ A'

  `$-subst : ∀ {Γ τ σ}{F : Γ , σ ⊢ τ}{A : Γ ⊢ σ}
    -> Value A
    -----------------------
    -> `λ F `$ A ⟶ F [ A ]

  `μ-step : ∀ {Γ τ}{T : Γ , τ ⊢ τ}
    --------------------------------
    -> `μ T ⟶ T [ `μ T ]

  `case-Z : ∀ {Γ τ}{T₀ : Γ ⊢ τ}{T₁ : Γ ⊢ `N `→ τ}
    --------------------------------
    -> `case `Z [Z T₀ |S T₁ ] ⟶ T₀

  `case-S : ∀ {Γ τ}{n : Γ ⊢ `N}{T₀ : Γ ⊢ τ}{T₁ : Γ ⊢ `N `→ τ}
    -> Value n
    -----------------------------------------
    -> `case `S n [Z T₀ |S T₁ ] ⟶ T₁ `$ n

  `let-step : ∀ {Γ τ σ}{T₀ T₀' : Γ ⊢ σ}{T₁ : Γ , σ ⊢ τ}
    -> T₀ ⟶ T₀'
    -----------------------------------------
    -> `let T₀ `in T₁ ⟶ `let T₀' `in T₁

  `let-subst : ∀ {Γ τ σ}{T₀ : Γ ⊢ σ}{T₁ : Γ , σ ⊢ τ}
    -> Value T₀
    -----------------------------------
    -> `let T₀ `in T₁ ⟶ T₁ [ T₀ ]

  `×-step₀ : ∀ {Γ τ σ}{L L' : Γ ⊢ τ}{R : Γ ⊢ σ}
    -> L ⟶ L'
    --------------------------
    -> L `, R ⟶ L' `, R

  `×-step₁ : ∀ {Γ τ σ}{L : Γ ⊢ τ}{R R' : Γ ⊢ σ}
    -> R ⟶ R'
    --------------------------
    -> L `, R ⟶ L `, R'

  `π₀-eval :  ∀ {Γ τ σ}{L : Γ ⊢ τ}{R : Γ ⊢ σ}
    ------------------------
    -> `π₀ L `, R ⟶ L

  `π₁-eval :  ∀ {Γ τ σ}{L : Γ ⊢ τ}{R : Γ ⊢ σ}
    ------------------------
    -> `π₁ L `, R ⟶ R

  `join-step : ∀ {Γ τ σ}{L L' : Γ ⊢ τ}{R R' : Γ ⊢ σ}
    -> L ⟶ L'
    -> R ⟶ R'
    --------------------------------------
    -> `join⟨ L , R ⟩ ⟶ `join⟨ L' , R' ⟩

  `join-step₀ : ∀ {Γ τ σ}{L L' : Γ ⊢ τ}{R : Γ ⊢ σ}
    -> L ⟶ L'
    -> Value R
    --------------------------------------
    -> `join⟨ L , R ⟩ ⟶ `join⟨ L' , R ⟩

  `join-step₁ : ∀ {Γ τ σ}{L : Γ ⊢ τ}{R R' : Γ ⊢ σ}
    -> Value L
    -> R ⟶ R'
    --------------------------------------
    -> `join⟨ L , R ⟩ ⟶ `join⟨ L , R' ⟩

  `join-eval :  ∀ {Γ τ σ}{L : Γ ⊢ τ}{R : Γ ⊢ σ}
    -> Value L
    -> Value R
    ------------------------------
    -> `join⟨ L , R ⟩ ⟶ L `, R
