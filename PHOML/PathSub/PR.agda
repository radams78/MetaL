module PHOML.PathSub.PR where
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.RP

_•PR_ : ∀ {U V W} → PathSub V W → Rep U V → PathSub U W
(τ •PR ρ) x = τ (ρ -Term x)

liftPathSub-•PR : ∀ {U V W} {τ : PathSub V W} {ρ : Rep U V} →
  liftPathSub (τ •PR ρ) ∼∼ (liftPathSub τ •PR liftRep _ ρ)
liftPathSub-•PR x₀ = refl
liftPathSub-•PR (↑ x) = refl

pathSub-•PR : ∀ {U V W} M {ρ : Rep U V} {τ : PathSub V W} {σ σ'} →
  M 〈 ρ 〉 ⟦⟦ τ ∶ σ ≡ σ' ⟧⟧ ≡ M ⟦⟦ τ •PR ρ ∶ σ •SR ρ ≡ σ' •SR ρ ⟧⟧
pathSub-•PR (var x) = refl
pathSub-•PR (app -bot []) = refl
pathSub-•PR (app -imp (φ ∷ (ψ ∷ []))) = cong₂ _⊃*_ (pathSub-•PR φ) (pathSub-•PR ψ)
pathSub-•PR (app (-lamTerm A) (M ∷ [])) {ρ} {τ} {σ} {σ'} = 
  cong (λλλ A) (let open ≡-Reasoning in
  begin
    M 〈 liftRep _ ρ 〉 ⟦⟦ liftPathSub τ ∶ sub↖ σ ≡ sub↗ σ' ⟧⟧
  ≡⟨ pathSub-•PR M ⟩
    M ⟦⟦ liftPathSub τ •PR liftRep _ ρ ∶ sub↖ σ •SR liftRep _ ρ ≡ sub↗ σ' •SR liftRep _ ρ ⟧⟧
  ≡⟨⟨ pathSub-cong M liftPathSub-•PR sub↖-•SR sub↗-•SR ⟩⟩
    M ⟦⟦ liftPathSub (τ •PR ρ) ∶ sub↖ (σ •SR ρ) ≡ sub↗ (σ' •SR ρ) ⟧⟧
  ∎)
pathSub-•PR (app -appTerm (M ∷ (N ∷ []))) = cong₄ app* (≡-sym (sub-•SR N)) (≡-sym (sub-•SR N)) (pathSub-•PR M) (pathSub-•PR N)

liftPathSub-upRep : ∀ {U V} {M : Term U} {τ : PathSub U V} {ρ σ} → M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ⇑ ⇑ ⇑ ≡ M ⇑ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧
liftPathSub-upRep {U} {V} {M} {τ} {ρ} {σ} = let open ≡-Reasoning in
  begin
    M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (pathSub-•RP (M))) ⟩⟩
    M ⟦⟦ upRep •RP τ ∶ upRep •RS ρ ≡ upRep •RS σ ⟧⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (pathSub-•RP (M)) ⟩⟩
    M ⟦⟦ upRep •RP (upRep •RP τ) ∶ upRep •RS (upRep •RS ρ) ≡ upRep •RS (upRep •RS σ) ⟧⟧ ⇑
  ≡⟨⟨ pathSub-•RP (M) ⟩⟩
    M ⟦⟦ upRep •RP (upRep •RP (upRep •RP τ)) ∶ upRep •RS (upRep •RS (upRep •RS ρ)) ≡ upRep •RS (upRep •RS (upRep •RS σ)) ⟧⟧
  ≡⟨⟩
    M ⟦⟦ liftPathSub τ •PR upRep ∶ sub↖ ρ •SR upRep ≡ sub↗ σ •SR upRep ⟧⟧
  ≡⟨⟨ pathSub-•PR (M) ⟩⟩
    M ⇑ ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧
  ∎

