module PHOML.Red.RRed where
open import Data.Bool
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red.Base

infix 10 _⇒?_
_⇒?_ : ∀ {V K} → Expression V K → Expression V K → Set
_⇒?_ = RClose _⇒_

--TODO Duplication below
⇒?-appTl : ∀ {V} {M M' N : Term V} → M ⇒? M' → appT M N ⇒? appT M' N
⇒?-appTl = respects-R _ _⇒_ (λ _ _ → appTl) _ _

⇒?-impl : ∀ {V} {φ φ' ψ : Term V} → φ ⇒? φ' → φ ⊃ ψ ⇒? φ' ⊃ ψ
⇒?-impl = respects-R _ _⇒_ (λ _ _ → impl) _ _

⇒?-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ⇒? ψ' → φ ⊃ ψ ⇒? φ ⊃ ψ'
⇒?-impr = respects-R _ _⇒_ (λ _ _ → impr) _ _

⇒?-imp*l : ∀ {V} {P P' Q : Path V} → P ⇒? P' → P ⊃* Q ⇒? P' ⊃* Q
⇒?-imp*l = respects-R _ _⇒_ (λ _ _ → imp*l) _ _

⇒?-imp*r : ∀ {V} {P Q Q' : Path V} → Q ⇒? Q' → P ⊃* Q ⇒? P ⊃* Q'
⇒?-imp*r = respects-R _ _⇒_ (λ _ _ → imp*r) _ _

⇒?-app*l : ∀ {V} {M N : Term V} {P P' Q} → P ⇒? P' → app* M N P Q ⇒? app* M N P' Q
⇒?-app*l = respects-R _ _⇒_ (λ _ _ → app*l) _ _

⇒?-appPl : ∀ {V} {δ δ' ε : Proof V} → δ ⇒? δ' → appP δ ε ⇒? appP δ' ε
⇒?-appPl = respects-R _ _⇒_ (λ _ _ → appPl) _ _

imp-osr-inj₁ : ∀ {V} {φ ψ χ : Term V} → φ ⊃ ψ ⇒ χ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
  (χ ≡ φ' ⊃ ψ' × φ ⇒? φ')
imp-osr-inj₁ {ψ = ψ} (impl {φ' = φ'} φ⊃φ') = φ' ,p ψ ,p refl ,p inc φ⊃φ'
imp-osr-inj₁ {φ = φ} (impr {ψ' = ψ'} _) = φ ,p ψ' ,p refl ,p ref

imp-osr-inj₂ : ∀ {V} {φ ψ χ : Term V} → φ ⊃ ψ ⇒ χ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
  (χ ≡ φ' ⊃ ψ' × ψ ⇒? ψ')
imp-osr-inj₂ {ψ = ψ} (impl {φ' = φ'} _) = φ' ,p ψ ,p refl ,p ref
imp-osr-inj₂ {φ = φ} (impr {ψ' = ψ'} ψ⇒ψ') = φ ,p ψ' ,p refl ,p inc ψ⇒ψ'

