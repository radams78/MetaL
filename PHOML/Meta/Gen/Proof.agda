module PHOML.Meta.Gen.Proof where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims.Closure
open import PHOML.Grammar
open import PHOML.Rules
open import PHOML.Red.Conv

generation-varP : ∀ {V} {Γ : Context V} {p : Var V -Proof} {ψ} → Γ ⊢ var p ∶ ψ → typeof p Γ ≃ ψ
generation-varP (varR _ _) = ref
generation-varP (convPR Γ⊢p∶ψ _ ψ≃ψ') = trans (generation-varP Γ⊢p∶ψ) ψ≃ψ'

generation-ΛP : ∀ {V} {Γ : Context V} {φ δ ψ} →
  Γ ⊢ ΛP φ δ ∶ ψ → Σ[ χ ∈ Term V ] (Γ ,P φ ⊢ δ ∶ χ ⇑ × ψ ≃ φ ⊃ χ)
generation-ΛP (ΛPR _ _ Γ,φ⊢δ∶ψ) = _ ,p Γ,φ⊢δ∶ψ ,p ref
generation-ΛP (convPR Γ⊢Λδ∶ψ Γ⊢ψ'∶Ω ψ≃ψ') =
  let χ ,p Γ,φ⊢δ∶χ ,p χ≃φ⊃ψ = generation-ΛP Γ⊢Λδ∶ψ in 
  χ ,p Γ,φ⊢δ∶χ ,p trans (sym ψ≃ψ') χ≃φ⊃ψ

generation-appP : ∀ {V} {Γ : Context V} {δ ε φ} → Γ ⊢ appP δ ε ∶ φ → 
  Σ[ ψ ∈ Term V ] Σ[ χ ∈ Term V ] (Γ ⊢ δ ∶ ψ ⊃ χ × Γ ⊢ ε ∶ ψ × χ ≃ φ)
generation-appP (appPR Γ⊢δ∶ψ⊃φ Γ⊢ε∶ψ) = _ ,p _ ,p Γ⊢δ∶ψ⊃φ ,p Γ⊢ε∶ψ ,p ref
generation-appP (convPR Γ⊢δε∶φ _ φ≃φ') = 
  let ψ ,p χ ,p Γ⊢δ∶ψ⊃χ ,p Γ⊢ε∶ψ ,p χ≃φ = generation-appP Γ⊢δε∶φ in
  ψ ,p χ ,p Γ⊢δ∶ψ⊃χ ,p Γ⊢ε∶ψ ,p trans χ≃φ φ≃φ'

generation-plus : ∀ {V Γ} {P : Path V} {φ} → Γ ⊢ plus P ∶ φ →
  Σ[ ψ ∈ Term V ] Σ[ χ ∈ Term V ] (Γ ⊢ P ∶ ψ ≡〈 Ω 〉 χ × φ ≃ ψ ⊃ χ)
generation-plus (convPR Γ⊢P+∶φ' Γ⊢φ∶Ω φ'≃φ) = 
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ'≃ψ⊃χ = generation-plus Γ⊢P+∶φ' in 
  ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p (trans (sym φ'≃φ) φ'≃ψ⊃χ)
generation-plus (plusR {φ = φ} {ψ = ψ} Γ⊢P∶φ≡ψ) = φ ,p ψ ,p Γ⊢P∶φ≡ψ ,p ref

generation-minus : ∀ {V Γ} {P : Path V} {φ} → Γ ⊢ minus P ∶ φ →
  Σ[ ψ ∈ Term V ] Σ[ χ ∈ Term V ] (Γ ⊢ P ∶ ψ ≡〈 Ω 〉 χ × φ ≃ χ ⊃ ψ)
generation-minus (convPR Γ⊢P+∶φ' Γ⊢φ∶Ω φ'≃φ) = 
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ'≃ψ⊃χ = generation-minus Γ⊢P+∶φ' in 
  ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p (trans (sym φ'≃φ) φ'≃ψ⊃χ)
generation-minus (minusR {φ = φ} {ψ = ψ} Γ⊢P∶φ≡ψ) = φ ,p ψ ,p Γ⊢P∶φ≡ψ ,p ref