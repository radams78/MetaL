module PHOML.PathSub.PS where
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.RP
open import PHOML.PathSub.PR

_∶_≡_•PS_ : ∀ {U V W} → PathSub V W → Sub V W → Sub V W → Sub U V → PathSub U W
(τ ∶ σ ≡ σ' •PS ρ) x = ρ _ x ⟦⟦ τ ∶ σ ≡ σ' ⟧⟧

•PS-congl : ∀ {U V W} {τ₁ τ₂ : PathSub V W} {σ₁ σ₂ σ₁' σ₂'} {ρ : Sub U V} → τ₁ ∼∼ τ₂ → σ₁ ∼ σ₂ → σ₁' ∼ σ₂' → (τ₁ ∶ σ₁ ≡ σ₁' •PS ρ) ∼∼ (τ₂ ∶ σ₂ ≡ σ₂' •PS ρ)
•PS-congl {ρ = ρ} τ₁∼∼τ₂ σ₁∼σ₂ σ₁'∼σ₂' x = pathSub-cong (ρ _ x) τ₁∼∼τ₂ σ₁∼σ₂ σ₁'∼σ₂'

liftPathSub-•PS : ∀ {U V W} {τ : PathSub V W} {ρ ρ' : Sub V W} {σ : Sub U V} →
  liftPathSub (τ ∶ ρ ≡ ρ' •PS σ) ∼∼ (liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' •PS liftSub _ σ)
liftPathSub-•PS x₀ = refl
liftPathSub-•PS {τ = τ} {ρ} {ρ'} {σ} (↑ x) = let open ≡-Reasoning in
  begin
    σ _ x ⟦⟦ τ ∶ ρ ≡ ρ' ⟧⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (pathSub-•RP (σ _ x))) ⟩⟩
    σ _ x ⟦⟦ upRep •RP τ ∶ upRep •RS ρ ≡ upRep •RS ρ' ⟧⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (pathSub-•RP (σ _ x)) ⟩⟩
    σ _ x ⟦⟦ upRep •RP (upRep •RP τ) ∶ upRep •RS (upRep •RS ρ) ≡ upRep •RS (upRep •RS ρ') ⟧⟧ ⇑
  ≡⟨⟨ pathSub-•RP (σ _ x) ⟩⟩
    σ _ x ⟦⟦ upRep •RP (upRep •RP (upRep •RP τ)) ∶ upRep •RS (upRep •RS (upRep •RS ρ)) ≡ upRep •RS (upRep •RS (upRep •RS ρ')) ⟧⟧
  ≡⟨⟩
    σ _ x ⟦⟦ liftPathSub τ •PR upRep ∶ sub↖ ρ •SR upRep ≡ sub↗ ρ' •SR upRep ⟧⟧
  ≡⟨⟨ pathSub-•PR (σ _ x) ⟩⟩
    σ _ x ⇑ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' ⟧⟧
  ∎

pathSub-•PS : ∀ {U V W} M {σ : Sub U V} {τ : PathSub V W} {ρ ρ'} →
  M ⟦⟦ τ ∶ ρ ≡ ρ' •PS σ ∶ ρ • σ ≡ ρ' • σ ⟧⟧ ≡ M ⟦ σ ⟧ ⟦⟦ τ ∶ ρ ≡ ρ' ⟧⟧
pathSub-•PS (var x) = refl
pathSub-•PS (app -bot []) = refl
pathSub-•PS (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathSub-•PS φ) (pathSub-•PS ψ)
pathSub-•PS (app (-lamTerm A) (M ∷ [])) {σ} {τ} {ρ} {ρ'} = cong (λλλ A) (let open ≡-Reasoning in
  begin
    M ⟦⟦ liftPathSub (τ ∶ ρ ≡ ρ' •PS σ) ∶ sub↖ (ρ • σ) ≡ sub↗ (ρ' • σ) ⟧⟧
  ≡⟨ pathSub-cong M liftPathSub-•PS sub↖-• sub↗-• ⟩
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' •PS liftSub _ σ ∶ sub↖ ρ • liftSub _ σ ≡ sub↗ ρ' • liftSub _ σ ⟧⟧
  ≡⟨ pathSub-•PS M ⟩
    M ⟦ liftSub _ σ ⟧ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ ρ' ⟧⟧
  ∎)
pathSub-•PS (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sub-• N) (sub-• N) (pathSub-•PS M) (pathSub-•PS N)

