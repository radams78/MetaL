--Computable proofs of canonical propositions
module PHOML.Compute.PC where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Canon.Prp
open import PHOML.Canon.Proof
open import PHOML.Neutral
open import PHOML.Red

⊧PC_∶_ : ∀ {V} → Proof V → CanonProp → Set
⊧PC_∶_ {V} δ bot = Σ[ ε ∈ NeutralP V ] δ ↠ decode-NeutralP ε
⊧PC_∶_ {V} δ (imp φ ψ) = ∀ W (ρ : Rep V W) (ε : Proof W) (⊧ε∶φ : ⊧PC ε ∶ φ) → ⊧PC appP (δ 〈 ρ 〉) ε ∶ ψ

⊧PCrep : ∀ {U V} {δ : Proof U} {ρ : Rep U V} {θ} → ⊧PC δ ∶ θ → ⊧PC δ 〈 ρ 〉 ∶ θ
⊧PCrep {δ = δ} {ρ = ρ} {θ = bot} (ν ,p δ↠ν) = nrepP ρ ν ,p subst (λ x → δ 〈 ρ 〉 ↠ x) (≡-sym (decode-nrepP {ρ = ρ} {ν})) (↠-resp-rep δ↠ν)
⊧PCrep {δ = δ} {ρ = ρ} {θ = imp θ θ'} ⊧δ∶θ⊃θ' W σ ε ⊧ε∶θ = subst (λ x → ⊧PC appP x ε ∶ θ') (rep-•R δ) (⊧δ∶θ⊃θ' W (σ •R ρ) ε ⊧ε∶θ)

⊧neutralPC : ∀ {V} (δ : NeutralP V) {θ : CanonProp} → ⊧PC decode-NeutralP δ ∶ θ
⊧neutralPC δ {θ = bot} = δ ,p ref
⊧neutralPC δ {θ = imp θ θ'} W ρ ε ⊧ε∶φ = subst (λ x → ⊧PC x ∶ θ') {appP (decode-NeutralP (nrepP ρ δ)) ε} (cong (λ x → appP x ε) (decode-nrepP {ρ = ρ} {δ})) (⊧neutralPC (app (nrepP ρ δ) ε))

expansionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC ε ∶ θ → δ ⇒ ε → ⊧PC δ ∶ θ
expansionPC {θ = bot} (χ ,p ε↠χ) δ⇒ε = χ ,p (trans (inc δ⇒ε) ε↠χ)
expansionPC {θ = imp θ θ'} ⊧ε∶θ⊃θ' δ⇒ε W ρ χ ⊧χ∶θ = expansionPC (⊧ε∶θ⊃θ' W ρ χ ⊧χ∶θ) (appPl (⇒-resp-rep δ⇒ε))

↞PC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC ε ∶ θ → δ ↠ ε → ⊧PC δ ∶ θ
↞PC ⊧ε∶θ (inc δ⇒ε) = expansionPC ⊧ε∶θ δ⇒ε
↞PC ⊧ε∶θ ref = ⊧ε∶θ
↞PC ⊧ε'∶θ (trans δ↠ε ε↠ε') = ↞PC (↞PC ⊧ε'∶θ ε↠ε') δ↠ε

reductionPC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC δ ∶ θ → δ ⇒ ε → ⊧PC ε ∶ θ
reductionPC {V} {ε = ε} {θ = bot} (ν ,p δ↠ν) δ⇒ε = 
  let cr ν' ν↠ν' ε↠ν' = diamond δ↠ν (inc δ⇒ε) in
  let ν₀ ,p ν'≡ν₀ = neutralP-red ν ν↠ν' refl in
  ν₀ ,p (subst (λ x → ε ↠ x) ν'≡ν₀ ε↠ν')
reductionPC {θ = imp θ θ'} ⊧δ∶θ⊃θ' δ⇒δ' W ρ ε ⊧ε∶θ = reductionPC {θ = θ'} (⊧δ∶θ⊃θ' W ρ ε ⊧ε∶θ) (appPl (⇒-resp-rep δ⇒δ'))

↠PC : ∀ {V} {δ ε : Proof V} {θ} → ⊧PC δ ∶ θ → δ ↠ ε → ⊧PC ε ∶ θ
↠PC ⊧δ∶θ (inc δ⇒ε) = reductionPC ⊧δ∶θ δ⇒ε
↠PC ⊧δ∶θ ref = ⊧δ∶θ
↠PC ⊧δ∶θ (trans δ↠ε ε↠ε') = ↠PC (↠PC ⊧δ∶θ δ↠ε) ε↠ε'
⊧PC-wn : ∀ {V} {δ : Proof V} {θ} → ⊧PC δ ∶ θ → Σ[ ε ∈ CanonP V ] δ ↠ decode-CanonP ε
⊧PC-wn {θ = bot} (ε ,p δ↠ε) = neutral ε ,p δ↠ε
⊧PC-wn {V} {δ} {θ = imp θ θ'} ⊧δ∶θ =
  let χ ,p δ⇑ε↠χ = ⊧PC-wn (⊧δ∶θ (V , -Proof) upRep (var x₀) (⊧neutralPC (var x₀))) in
  let χ' ,p δ⇑↠χ' = app-wnl' {χ = χ} δ⇑ε↠χ refl refl in
  let χ'' ,p δ↠χ'' ,p χ''⇑≡χ' = ↠-reflect-rep {E = δ} {ρ = upRep} δ⇑↠χ' refl in  
  let χ''' ,p χ'''⇑≡χ'' = reflect-CanonP {δ = χ''} {χ = χ'} χ''⇑≡χ' in
  χ''' ,p subst (λ x → δ ↠ x) χ'''⇑≡χ'' δ↠χ''

