module PHOML.PathSub.SP where
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.PS

infix 25 _•SP_
_•SP_ : ∀ {U V W} → Sub V W → PathSub U V → PathSub U W
(σ •SP τ) x = τ x ⟦ σ ⟧

liftPathSub-SP : ∀ {U V W} {τ : PathSub U V} {μ : Sub V W} → liftPathSub (μ •SP τ) ∼∼ liftsSub pathDom μ •SP liftPathSub τ
liftPathSub-SP x₀ = refl
liftPathSub-SP {τ = τ} (↑ x) = ≡-sym (liftSub-upRep₃ (τ x))

pathSub-•SP : ∀ {U V W} (E : Term U) {τ : PathSub U V} {ρ σ} {μ : Sub V W} →
  E ⟦⟦ μ •SP τ ∶ μ • ρ ≡ μ • σ ⟧⟧ ≡ E ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ⟦ μ ⟧
pathSub-•SP (var _) = refl
pathSub-•SP (app -bot []) = refl
pathSub-•SP (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathSub-•SP φ) (pathSub-•SP ψ)
pathSub-•SP (app (-lamTerm A) (M ∷ [])) {τ} {ρ} {σ} {μ} = cong (λλλ A) (let open ≡-Reasoning in 
  begin
    M ⟦⟦ liftPathSub (μ •SP τ) ∶ sub↖ (μ • ρ) ≡ sub↗ (μ • σ) ⟧⟧
  ≡⟨ pathSub-cong M liftPathSub-SP sub↖-comp sub↗-comp ⟩
    M ⟦⟦ liftsSub pathDom μ •SP liftPathSub τ ∶ liftsSub pathDom μ • sub↖ ρ ≡ liftsSub pathDom μ • sub↗ σ ⟧⟧
  ≡⟨ pathSub-•SP M ⟩
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧ ⟦ liftsSub pathDom μ ⟧
  ∎)
pathSub-•SP (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sub-• N) (sub-• N) (pathSub-•SP M) (pathSub-•SP N)

•SP-botSub : ∀ {U V} {τ : PathSub U V} {ρ σ M} → 
  (τ ∶ ρ ≡ σ •PS (x₀:= M)) ∼∼ ((x₂:= M ⟦ ρ ⟧ ,x₁:= M ⟦ σ ⟧ ,x₀:= M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧) •SP liftPathSub τ)
•SP-botSub x₀ = refl
•SP-botSub {τ = τ} {ρ} {σ} {M} (↑ x) = ≡-sym botSub-upRep₃

