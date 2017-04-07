module PHOML.Meta.TypeVal where
open import Prelims
open import PHOML.Grammar
open import PHOML.Rules
open import PHOML.Meta.ConVal
open import PHOML.Meta.Gen

prop-validity : ∀ {V} {Γ : Context V} {δ : Proof V} {φ : Term V} → Γ ⊢ δ ∶ φ → Γ ⊢ φ ∶ ty Ω
eq-validity₁ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ M ∶ ty A
eq-validity₂ : ∀ {V} {Γ : Context V} {P : Path V} {E M A N} → Γ ⊢ P ∶ E → E ≡ M ≡〈 A 〉 N → Γ ⊢ N ∶ ty A

prop-validity (varR _ validΓ) = context-validity-Prop validΓ
prop-validity (appPR Γ⊢δ∶φ⊃ψ _) = generation-⊃₂ (prop-validity Γ⊢δ∶φ⊃ψ)
prop-validity (ΛPR Γ⊢φ∶Ω Γ⊢ψ∶Ω _) = ⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω
prop-validity (convPR _ Γ⊢φ∶Ω _) = Γ⊢φ∶Ω
prop-validity (plusR Γ⊢P∶φ≡ψ) = ⊃R (eq-validity₁ Γ⊢P∶φ≡ψ refl) (eq-validity₂ Γ⊢P∶φ≡ψ refl)
prop-validity (minusR Γ⊢P∶φ≡ψ) = ⊃R (eq-validity₂ Γ⊢P∶φ≡ψ refl) (eq-validity₁ Γ⊢P∶φ≡ψ refl)

eq-validity₁ (varR {Γ = Γ} _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ left E ∶ ty (type E)) E≡M≡N (context-validity-Eq₁ validΓ)
eq-validity₁ {Γ = Γ} (refR Γ⊢P∶M≡N) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢P∶M≡N
eq-validity₁ {Γ = Γ} (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') E≡φ⊃ψ≡φ'⊃ψ' = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡φ⊃ψ≡φ'⊃ψ') (eq-inj₂ E≡φ⊃ψ≡φ'⊃ψ') (⊃R (eq-validity₁ Γ⊢P∶φ≡φ' refl) (eq-validity₁ Γ⊢Q∶ψ≡ψ' refl))
eq-validity₁ {Γ = Γ} (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) E≡φ≡ψ = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡φ≡ψ) (eq-inj₂ E≡φ≡ψ) (generation-⊃₂ (prop-validity Γ⊢ε∶ψ⊃φ))
eq-validity₁ {Γ = Γ} (lllR Γ⊢M∶A _ _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M∶A
eq-validity₁ {Γ = Γ} (appER Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) (appTR (eq-validity₁ Γ⊢P∶M≡M' refl) Γ⊢N∶A)
eq-validity₁ {Γ = Γ} (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₁ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M'∶A

eq-validity₂ {Γ = Γ} (varR _ validΓ) E≡M≡N = subst (λ E → Γ ⊢ right E ∶ ty (type E)) E≡M≡N (context-validity-Eq₂ validΓ)
eq-validity₂ {Γ = Γ} (refR Γ⊢M∶A) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢M∶A
eq-validity₂ {Γ = Γ} (⊃*R Γ⊢P∶φ≡ψ Γ⊢Q∶φ'≡ψ') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (⊃R (eq-validity₂ Γ⊢P∶φ≡ψ refl) (eq-validity₂ Γ⊢Q∶φ'≡ψ' refl))
eq-validity₂ {Γ = Γ} (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (generation-⊃₂ (prop-validity Γ⊢δ∶φ⊃ψ))
eq-validity₂ {Γ = Γ} (lllR _ Γ⊢N∶A⇛B _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢N∶A⇛B
eq-validity₂ {Γ = Γ} (appER Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) (appTR (eq-validity₂ Γ⊢P∶M≡M' refl) Γ⊢N'∶A)
eq-validity₂ {Γ = Γ} (convER _ _ Γ⊢N'∶A _ _) E≡M≡N = subst₂ (λ x y → Γ ⊢ x ∶ ty y) (eq-inj₃ E≡M≡N) (eq-inj₂ E≡M≡N) Γ⊢N'∶A

