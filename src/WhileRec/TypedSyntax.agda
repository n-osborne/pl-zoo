module WhileRec.TypedSyntax where

open import WhileRec.Ty

infixr 8 S_
infixr 7 `S_ `λ_∙_ `fix_ `!_
infixl 6 _,_ _`$_ _++_ 
infixr 4 _`←_ `while_`do_
infix  3 _⊢_ _∋_

data db : Set where
  Z : db
  S_ : db -> db

data Term : Ty -> Set where

  `skp : Term `1

  `Z : Term `N

  `S_ : Term `N -> Term `N

  `V : (τ : Ty) -> db -> Term (`ref τ)

  `!_ : ∀ {τ} -> Term (`ref τ) -> Term τ

  `λ_∙_ : ∀ {τ} -> (σ : Ty) -> Term τ -> Term (σ `⇒ τ)

  _`$_ : ∀ {τ σ} -> Term (τ `⇒ σ) -> Term τ -> Term σ

  `fix_ : ∀ {τ} -> Term τ -> Term τ

  `case_[Z_|Sn_] : ∀ {τ} -> Term `N -> Term τ -> Term τ -> Term τ

  `let : ∀ {τ} -> Term τ -> Term `1

  _`←_ : ∀ {τ} -> Term (`ref τ) -> Term τ -> Term `1

  `while_`do_ : Term `N -> Term `1 -> Term `1

  _`,_ : ∀ {τ} -> Term `1 -> Term τ -> Term τ

data Ctx : Set where
  ε : Ctx
  _,_ : Ctx -> Ty -> Ctx

_++_ : Ctx -> Ctx -> Ctx
c ++ ε        = c
c ++ (c1 , x) = (c ++ c1) , x

data _∋_ : Ctx -> db -> Set where
  here : ∀ {Γ} -> (τ : Ty) -> Γ , τ ∋ Z
  there : ∀ {Γ τ d} -> Γ ∋ d -> Γ , τ ∋ S d

getTy : ∀ {i}{Γ : Ctx} -> Γ ∋ i -> Ty
getTy (here τ) = τ
getTy (there p) = getTy p

data _⊢_ : ∀ {τ} -> Ctx -> Term τ -> Set where
  `skp-wt   : ∀ {Γ}
              -----------
              -> Γ ⊢ `skp
              
  `Z-wt     : ∀ {Γ}
              ---------
              -> Γ ⊢ `Z
              
  `S-wt     : ∀ {Γ}{n : Term `N}
              -> Γ ⊢ n
              -----------
              -> Γ ⊢ `S n
              
  `V-wt     : ∀ {Γ i}
              -> (p : Γ ∋ i)
              ---------------------
              -> Γ ⊢ `V (getTy p) i
              
  `!-wt     : ∀ {Γ τ}{v : Term (`ref τ)}
              -> Γ ⊢ v
              -----------
              -> Γ ⊢ `! v
              
  `λ-wt     : ∀ {Γ τ σ}{t : Term τ}
              -> Γ , σ ⊢ t
              ---------------
              -> Γ ⊢ `λ σ ∙ t
              
  `$-wt     : ∀ {Γ τ σ}{f : Term (σ `⇒ τ)}{a : Term σ}
              -> Γ ⊢ f
              -> Γ ⊢ a
              -------------
              -> Γ ⊢ f `$ a
              
  `fix-wt   : ∀ {Γ τ}(t : Term τ)
              -> Γ , τ ⊢ t
              -------------
              -> Γ ⊢ `fix t
              
  `case-wt  : ∀ {Γ τ}{n : Term `N}{t₀ t₁ : Term τ}
              -> Γ ⊢ n
              -> Γ ⊢ t₀
              -> Γ , `N ⊢ t₁
              -----------------------------
              -> Γ ⊢ `case n [Z t₀ |Sn t₁ ]
              
  `let-wt   : ∀ {Γ τ}{t : Term τ}
              -> Γ ⊢ t
              -------------
              -> Γ ⊢ `let t
              
  `←wt      : ∀ {Γ τ}{v : Term (`ref τ)}{t : Term τ}
              -> Γ ⊢ v
              -> Γ ⊢ t
              ------------
              -> Γ ⊢ v `← t
              
  `while-wt : ∀ {Γ}{n : Term `N}{t : Term `1}
              -> Γ ⊢ n
              -> Γ ⊢ t
              ---------------------
              -> Γ ⊢ `while n `do t
              
  `,-wt     : ∀ {Γ τ}{t₀ : Term `1}{t₁ : Term τ}
              -> Γ ⊢ t₀
              -> Γ ⊢ t₁
              ---------------
              -> Γ ⊢ t₀ `, t₁


