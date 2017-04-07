module PHOML.Meta.Gen.Path where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules
open import PHOML.Meta.ConVal

generation-varE : ∀ {V} {Γ : Context V} {e : Var V -Path} {T M A N} →
  Γ ⊢ var e ∶ T → T ≡ M ≡〈 A 〉 N → Σ[ M' ∈ Term V ] Σ[ N' ∈ Term V ] (typeof e Γ ≡ M' ≡〈 A 〉 N' × M ≃ M' × N ≃ N')
generation-varE (varR e validΓ) T≡M≡N = _ ,p _ ,p T≡M≡N ,p ref ,p ref
generation-varE (convER {M = M} {N = N} Γ⊢e∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') M'≡N'≡M≡N =
  let M'' ,p N'' ,p M≡N≡M''≡N'' ,p M≃M'' ,p N≃N'' = generation-varE Γ⊢e∶M≡N refl in 
  M'' ,p N'' ,p (≡-trans M≡N≡M''≡N'' (cong (λ A → M'' ≡〈 A 〉 N'') (eq-inj₂ M'≡N'≡M≡N))) ,p 
  trans (subst (λ x → x ≃ M) (eq-inj₁ M'≡N'≡M≡N) (sym M≃M')) M≃M'' ,p 
  trans (subst (λ x → x ≃ N) (eq-inj₃ M'≡N'≡M≡N) (sym N≃N')) N≃N''

generation-reff₁ : ∀ {V} {Γ : Context V} {M N N' : Term V} {A} → Γ ⊢ reff M ∶ N ≡〈 A 〉 N' → Γ ⊢ M ∶ ty A
generation-reff₁ (refR Γ⊢M∶A) = Γ⊢M∶A
generation-reff₁ (convER Γ⊢refM∶N≡N' _ _ _ _) = generation-reff₁ Γ⊢refM∶N≡N'

generation-reff₂ : ∀ {V} {Γ : Context V} {M N N' : Term V} {A} → Γ ⊢ reff M ∶ N ≡〈 A 〉 N' → M ≃ N
generation-reff₂ (refR _) = ref
generation-reff₂ (convER Γ⊢refM∶N≡N' _ _ M≃M' _) = trans (generation-reff₂ Γ⊢refM∶N≡N') M≃M'

generation-reff₃ : ∀ {V} {Γ : Context V} {M N N' : Term V} {A} → Γ ⊢ reff M ∶ N ≡〈 A 〉 N' → M ≃ N'
generation-reff₃ (refR _) = ref
generation-reff₃ (convER Γ⊢refM∶N≡N' _ _ _ N≃N') = trans (generation-reff₃ Γ⊢refM∶N≡N') N≃N'

generation-⊃* : ∀ {V} {Γ} {P Q : Path V} {φ A φ'} → Γ ⊢ P ⊃* Q ∶ φ ≡〈 A 〉 φ' →
  Σ[ ψ ∈ Term V ] Σ[ ψ' ∈ Term V ] Σ[ χ ∈ Term V ] Σ[ χ' ∈ Term V ]
  (Γ ⊢ P ∶ ψ ≡〈 Ω 〉 ψ' × Γ ⊢ Q ∶ χ ≡〈 Ω 〉 χ' × φ ≃ ψ ⊃ χ × φ' ≃ ψ' ⊃ χ' × A ≡ Ω)
generation-⊃* (⊃*R {φ = ψ} {ψ'} {χ} {χ'} Γ⊢P∶ψ≡ψ' Γ⊢Q∶χ≡χ') = ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢P∶ψ≡ψ' ,p Γ⊢Q∶χ≡χ' ,p ref ,p ref ,p refl
generation-⊃* (convER Γ⊢P⊃*Q∶φ≡φ' Γ⊢φ₁∶Ω Γ⊢φ₁'∶Ω φ≃φ₁ φ'≃φ₁') = 
  let ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢P∶ψ≡ψ' ,p Γ⊢Q∶χ≡χ' ,p φ₁≃ψ⊃χ ,p φ₁'≃ψ'⊃χ' ,p A≡Ω = generation-⊃* Γ⊢P⊃*Q∶φ≡φ' in 
  ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢P∶ψ≡ψ' ,p Γ⊢Q∶χ≡χ' ,p trans (sym φ≃φ₁) φ₁≃ψ⊃χ ,p (trans (sym φ'≃φ₁') φ₁'≃ψ'⊃χ') ,p A≡Ω

generation-univ₁ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → φ ≃ M
generation-univ₁ (univR _ _) = ref
generation-univ₁ (convER Γ⊢univδε∶M≡N _ _ M≃M' _) = trans (generation-univ₁ Γ⊢univδε∶M≡N) M≃M'

generation-univ₂ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → ψ ≃ N
generation-univ₂ (univR _ _) = ref
generation-univ₂ (convER Γ⊢univδε∶M≡N _ _ _ N≃N') = trans (generation-univ₂ Γ⊢univδε∶M≡N) N≃N'

generation-univ₃ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → Γ ⊢ δ ∶ φ ⊃ ψ
generation-univ₃ (univR Γ⊢δ∶M⊃N _) = Γ⊢δ∶M⊃N
generation-univ₃ (convER Γ⊢univδε∶M≡N _ _ _ _) = generation-univ₃ Γ⊢univδε∶M≡N

generation-univ₄ : ∀ {V} {Γ : Context V} {φ ψ δ ε M A N} → Γ ⊢ univ φ ψ δ ε ∶ M ≡〈 A 〉 N → Γ ⊢ ε ∶ ψ ⊃ φ
generation-univ₄ (univR _ Γ⊢ε∶N⊃M) = Γ⊢ε∶N⊃M
generation-univ₄ (convER Γ⊢univδε∶M≡N _ _ _ _) = generation-univ₄ Γ⊢univδε∶M≡N

generation-λλλ : ∀ {V} {Γ : Context V} {A P M B N} →
  Γ ⊢ λλλ A P ∶ M ≡〈 B 〉 N → Σ[ C ∈ Type ] (addpath Γ A ⊢ P ∶ appT (M ⇑ ⇑ ⇑) (var x₂) ≡〈 C 〉 appT (N ⇑ ⇑ ⇑) (var x₁) × B ≡ A ⇛ C)
generation-λλλ (lllR {B = C} _ _ Γ⊢P∶Mx≡Ny) = C ,p Γ⊢P∶Mx≡Ny ,p refl
generation-λλλ {Γ = Γ} {A = A} (convER {M = M} {M' = M'} {N' = N'}  Γ⊢ΛP∶M≡N Γ⊢M'∶B Γ⊢N'∶B M≃M' N≃N') = 
  let C ,p Γ⊢P∶Mx≡Ny ,p B≡A⇛C = generation-λλλ Γ⊢ΛP∶M≡N in
  C ,p 
  let validΓ : valid Γ
      validΓ = context-validity Γ⊢ΛP∶M≡N in
  let validΓA : valid (Γ ,T A)
      validΓA = ctxTR validΓ in
  let ΓAAE⊢M'∶A⇛C : addpath Γ A ⊢ M' ⇑ ⇑ ⇑ ∶ ty (A ⇛ C)
      ΓAAE⊢M'∶A⇛C = weakening (weakening (weakening (change-type Γ⊢M'∶B (cong ty B≡A⇛C)) validΓA (upRep-typed (ty A))) (ctxTR validΓA) (upRep-typed (ty A))) (valid-addpath validΓ) (upRep-typed (var x₁ ≡〈 A 〉 var x₀)) in 
  let ΓAAE⊢N'∶A⇛C : addpath Γ A ⊢ N' ⇑ ⇑ ⇑ ∶ ty (A ⇛ C)
      ΓAAE⊢N'∶A⇛C = weakening (weakening (weakening (change-type Γ⊢N'∶B (cong ty B≡A⇛C)) validΓA (upRep-typed (ty A))) (ctxTR validΓA) (upRep-typed (ty A))) (valid-addpath validΓ) (upRep-typed (var x₁ ≡〈 A 〉 var x₀)) in 
  convER Γ⊢P∶Mx≡Ny (appTR ΓAAE⊢M'∶A⇛C (varR x₂ (valid-addpath validΓ))) (appTR ΓAAE⊢N'∶A⇛C (varR x₁ (valid-addpath validΓ))) 
  (≃-appTl (≃-resp-rep (≃-resp-rep (≃-resp-rep M≃M')))) 
  (≃-appTl (≃-resp-rep (≃-resp-rep (≃-resp-rep N≃N')))) ,p 
  B≡A⇛C

generation-app* : ∀ {V} {Γ : Context V} {P : Path V} {M N Q L B L'} →
  Γ ⊢ app* M N P Q ∶ L ≡〈 B 〉 L' →
  Σ[ A ∈ Type ] Σ[ F ∈ Term V ] Σ[ G ∈ Term V ] (Γ ⊢ P ∶ F ≡〈 A ⇛ B 〉 G × Γ ⊢ Q ∶ M ≡〈 A 〉 N × appT F M ≃ L × appT G N ≃ L')
generation-app* (appER {M = F} {M' = G} {A = A} Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶F≡G Γ⊢Q∶N≡N') = A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶N≡N' ,p ref ,p ref
generation-app* (convER Γ⊢PQ∶L≡L' _ _ L≃L₁ L'≃L₁') = 
  let A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p FM≃L ,p GN≃L' = generation-app* Γ⊢PQ∶L≡L' in
  A ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p trans FM≃L L≃L₁ ,p trans GN≃L' L'≃L₁'

