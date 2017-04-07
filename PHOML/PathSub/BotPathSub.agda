module PHOML.PathSub.BotPathSub where
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.RP
open import PHOML.PathSub.PR

x₀::= : ∀ {V} → Path V → PathSub (V , -Term) V
(x₀::= P) x₀ = P
(x₀::= P) (↑ x) = reff (var x)

botPathSub-liftRep' : ∀ {U V} {ρ : Rep U V} {P : Path U} →
  (ρ •RP x₀::= P) ∼∼ (x₀::= (P 〈 ρ 〉) •PR liftRep -Term ρ)
botPathSub-liftRep' x₀ = refl
botPathSub-liftRep' (↑ x) = refl

botPathSub-liftRep : ∀ {U V} {M : Term (U , -Term)} {P N N'} {ρ : Rep U V} →
  M ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧ 〈 ρ 〉 ≡ M 〈 liftRep -Term ρ 〉 ⟦⟦ x₀::= (P 〈 ρ 〉) ∶ x₀:= N 〈 ρ 〉 ≡ x₀:= N' 〈 ρ 〉 ⟧⟧
botPathSub-liftRep {U} {V} {M} {P} {N} {N'} {ρ} = let open ≡-Reasoning in
    begin
      M ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧ 〈 ρ 〉
    ≡⟨⟨ pathSub-•RP M ⟩⟩
      M ⟦⟦ ρ •RP x₀::= P ∶ ρ •RS x₀:= N ≡ ρ •RS x₀:= N' ⟧⟧
    ≡⟨ pathSub-cong M botPathSub-liftRep' •RS-botSub' •RS-botSub' ⟩
      M ⟦⟦ x₀::= (P 〈 ρ 〉) •PR liftRep -Term ρ ∶ x₀:= N 〈 ρ 〉 •SR liftRep -Term ρ ≡ x₀:= N' 〈 ρ 〉 •SR liftRep -Term ρ ⟧⟧
    ≡⟨⟨ pathSub-•PR M ⟩⟩
      M 〈 liftRep -Term ρ 〉 ⟦⟦ x₀::= (P 〈 ρ 〉) ∶ x₀:= N 〈 ρ 〉 ≡ x₀:= N' 〈 ρ 〉 ⟧⟧
    ∎
