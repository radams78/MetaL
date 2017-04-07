module PHOML.Meta.SubRed where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Rules
open import PHOML.Meta.Gen
open import PHOML.Meta.Sub
open import PHOML.Meta.ConVal
open import PHOML.Meta.TypeVal
open import PHOML.Meta.PathSub

subject-reduction-⇒ : ∀ {V} {K} {E F : Expression V (varKind K)} {Γ} {A} →
  Γ ⊢ E ∶ A → E ⇒ F → Γ ⊢ F ∶ A
subject-reduction-⇒ {A = app (-ty B) []} Γ⊢ΛMN∶B βT = 
  let C ,p Γ⊢ΛM∶C⇛B ,p Γ⊢N∶C = generation-appT Γ⊢ΛMN∶B in
  let D ,p Γ,A⊢M∶D ,p C⇛B≡A⇛D = generation-ΛT Γ⊢ΛM∶C⇛B in
  change-type (substitution Γ,A⊢M∶D (context-validity Γ⊢ΛMN∶B) (botSub-typed (change-type Γ⊢N∶C (cong ty (⇛-injl C⇛B≡A⇛D))))) 
  (cong ty (≡-sym (⇛-injr C⇛B≡A⇛D)))
subject-reduction-⇒ {A = app (-ty A) []} Γ⊢MN∶A (appTl M⇒M') = 
  let B ,p Γ⊢M∶B⇛A ,p Γ⊢N∶B = generation-appT Γ⊢MN∶A in
  appTR (subject-reduction-⇒ Γ⊢M∶B⇛A M⇒M') Γ⊢N∶B
subject-reduction-⇒ {A = app (-ty A) []} Γ⊢φ⊃ψ∶Ω (impl φ⇒φ') = 
  let Γ⊢φ∶Ω = generation-⊃₁ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢ψ∶Ω = generation-⊃₂ Γ⊢φ⊃ψ∶Ω in
  let A≡Ω = generation-⊃₃ Γ⊢φ⊃ψ∶Ω in
  change-type (⊃R (subject-reduction-⇒ Γ⊢φ∶Ω φ⇒φ') Γ⊢ψ∶Ω) (cong ty (≡-sym A≡Ω))
subject-reduction-⇒ {A = app (-ty A) []} Γ⊢φ⊃ψ∶Ω (impr ψ⇒ψ') = 
  let Γ⊢φ∶Ω = generation-⊃₁ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢ψ∶Ω = generation-⊃₂ Γ⊢φ⊃ψ∶Ω in
  let A≡Ω = generation-⊃₃ Γ⊢φ⊃ψ∶Ω in
  change-type (⊃R Γ⊢φ∶Ω (subject-reduction-⇒ Γ⊢ψ∶Ω ψ⇒ψ')) (cong ty (≡-sym A≡Ω))
subject-reduction-⇒ {A = ψ} Γ⊢Λδε∶ψ (βP {ε = ε}) = 
  let φ' ,p ψ' ,p Γ⊢Λδ∶φ'⊃ψ' ,p Γ⊢ε∶φ' ,p ψ'≃ψ = generation-appP Γ⊢Λδε∶ψ in
  let χ ,p Γ,φ⊢δ∶χ ,p φ'⊃ψ'≃φ⊃χ = generation-ΛP Γ⊢Λδ∶φ'⊃ψ' in
  convPR (substitution Γ,φ⊢δ∶χ (context-validity Γ⊢Λδε∶ψ) (botSub-typed (convPR Γ⊢ε∶φ' (context-validityP (context-validity Γ,φ⊢δ∶χ)) 
    (≃-⊃-injl φ'⊃ψ'≃φ⊃χ)))) (prop-validity Γ⊢Λδε∶ψ) (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      χ ⇑ ⟦ x₀:= ε ⟧
    ≡⟨ botSub-upRep χ ⟩
      χ
    ≈⟨⟨ ≃-⊃-injr φ'⊃ψ'≃φ⊃χ ⟩⟩
      ψ'
    ≈⟨ ψ'≃ψ ⟩
      ψ
    ∎)
subject-reduction-⇒ Γ⊢δε∶φ (appPl δ⇒δ') = 
  let ψ ,p φ' ,p Γ⊢δ∶ψ⊃φ' ,p Γ⊢ε∶ψ ,p φ'≃φ = generation-appP Γ⊢δε∶φ in 
  convPR (appPR (subject-reduction-⇒ Γ⊢δ∶ψ⊃φ' δ⇒δ') Γ⊢ε∶ψ) (prop-validity Γ⊢δε∶φ) φ'≃φ
subject-reduction-⇒ {Γ = Γ} Γ⊢reffM+∶φ (refdir {φ = M} {d = -plus}) = 
  let ψ ,p χ ,p Γ⊢reffM∶ψ≡χ ,p φ≃ψ⊃χ = generation-plus Γ⊢reffM+∶φ in
  let Γ⊢M∶Ω : Γ ⊢ M ∶ ty Ω
      Γ⊢M∶Ω = generation-reff₁ Γ⊢reffM∶ψ≡χ in
  convPR (ΛPR Γ⊢M∶Ω Γ⊢M∶Ω (varR x₀ (ctxPR Γ⊢M∶Ω))) (prop-validity Γ⊢reffM+∶φ) (trans (≃-imp (generation-reff₂ Γ⊢reffM∶ψ≡χ) (generation-reff₃ Γ⊢reffM∶ψ≡χ)) (sym φ≃ψ⊃χ))
subject-reduction-⇒ {Γ = Γ} Γ⊢reffM+∶φ (refdir {φ = M} {d = -minus}) = 
  let ψ ,p χ ,p Γ⊢reffM∶ψ≡χ ,p φ≃ψ⊃χ = generation-minus Γ⊢reffM+∶φ in
  let Γ⊢M∶Ω : Γ ⊢ M ∶ ty Ω
      Γ⊢M∶Ω = generation-reff₁ Γ⊢reffM∶ψ≡χ in
  convPR (ΛPR Γ⊢M∶Ω Γ⊢M∶Ω (varR x₀ (ctxPR Γ⊢M∶Ω))) (prop-validity Γ⊢reffM+∶φ) (trans (≃-imp (generation-reff₃ Γ⊢reffM∶ψ≡χ) (generation-reff₂ Γ⊢reffM∶ψ≡χ)) (sym φ≃ψ⊃χ))
subject-reduction-⇒ Γ⊢univδε+∶φ univplus = 
  let ψ ,p χ ,p Γ⊢univδε∶ψ≡χ ,p φ≃ψ⊃χ = generation-plus Γ⊢univδε+∶φ in 
  convPR (generation-univ₃ Γ⊢univδε∶ψ≡χ) (prop-validity Γ⊢univδε+∶φ) (trans (≃-imp (generation-univ₁ Γ⊢univδε∶ψ≡χ) (generation-univ₂ Γ⊢univδε∶ψ≡χ)) (sym φ≃ψ⊃χ))
subject-reduction-⇒ Γ⊢univδε-∶φ univminus = 
  let ψ ,p χ ,p Γ⊢univδε∶ψ≡χ ,p φ≃χ⊃ψ = generation-minus Γ⊢univδε-∶φ in 
  convPR (generation-univ₄ Γ⊢univδε∶ψ≡χ) (prop-validity Γ⊢univδε-∶φ) (trans (≃-imp (generation-univ₂ Γ⊢univδε∶ψ≡χ) (generation-univ₁ Γ⊢univδε∶ψ≡χ)) (sym φ≃χ⊃ψ))
subject-reduction-⇒ Γ⊢P+∶φ (dirR {d = -plus} P⇒Q) = 
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ≃ψ⊃χ = generation-plus Γ⊢P+∶φ in 
  convPR (plusR (subject-reduction-⇒ Γ⊢P∶ψ≡χ P⇒Q)) (prop-validity Γ⊢P+∶φ) (sym φ≃ψ⊃χ)
subject-reduction-⇒ Γ⊢P-∶φ (dirR {d = -minus} P⇒Q) =
  let ψ ,p χ ,p Γ⊢P∶ψ≡χ ,p φ≃χ⊃ψ = generation-minus Γ⊢P-∶φ in 
  convPR (minusR (subject-reduction-⇒ Γ⊢P∶ψ≡χ P⇒Q)) (prop-validity Γ⊢P-∶φ) (sym φ≃χ⊃ψ)
subject-reduction-⇒ {Γ = Γ} {A = app (-eq B) (L ∷ (L' ∷ []))} Γ⊢ΛPQ∶L≡L' (βE {A = A} {M} {N} {P} {Q}) = 
  let C ,p F ,p G ,p Γ⊢ΛP∶F≡G ,p Γ⊢Q∶M≡N ,p FM≃L ,p GN≃L' = generation-app* Γ⊢ΛPQ∶L≡L' in
  let D ,p ΓAAE⊢P∶Fx≡Gy ,p C⇛B≡A⇛D = generation-λλλ Γ⊢ΛP∶F≡G in
  let C≡A : C ≡ A
      C≡A = ⇛-injl C⇛B≡A⇛D in
  let tyC≡tyA : ty C ≡ ty A
      tyC≡tyA = cong ty C≡A in
  convER (substitution (subst (λ x → addpath Γ A ⊢ P ∶ appT (F ⇑ ⇑ ⇑) (var x₂) ≡〈 x 〉 appT (G ⇑ ⇑ ⇑) (var x₁)) 
    (≡-sym (⇛-injr C⇛B≡A⇛D)) 
    ΓAAE⊢P∶Fx≡Gy) 
    (context-validity Γ⊢ΛPQ∶L≡L') 
    (botSub₃-typed (change-type (eq-validity₁ Γ⊢Q∶M≡N refl) tyC≡tyA) 
      (change-type (eq-validity₂ Γ⊢Q∶M≡N refl) tyC≡tyA) 
      (subst (λ x → Γ ⊢ Q ∶ M ≡〈 x 〉 N) C≡A Γ⊢Q∶M≡N))) 
    (eq-validity₁ Γ⊢ΛPQ∶L≡L' refl) 
    (eq-validity₂ Γ⊢ΛPQ∶L≡L' refl) 
    (subst₂ _≃_ (cong₂ appT (≡-sym botSub-upRep₃) refl) refl FM≃L) 
    (subst₂ _≃_ (cong₂ appT (≡-sym botSub-upRep₃) refl) refl GN≃L')
subject-reduction-⇒ {Γ = Γ} {A = app (-eq A) (M ∷ (M' ∷ []))} Γ⊢refΛLP∶M≡M' (βPP {A = C} {M = L} {N = N} {N' = N'} {P = P}) =
  let B ,p F ,p G ,p Γ⊢refΛL∶F≡G ,p Γ⊢P∶N≡N' ,p FN≃M ,p GN'≃M' = generation-app* Γ⊢refΛLP∶M≡M' in
  let Γ⊢ΛL∶B⇛A : Γ ⊢ ΛT C L ∶ ty (B ⇛ A)
      Γ⊢ΛL∶B⇛A = generation-reff₁ Γ⊢refΛL∶F≡G in
  let ΛL≃F : ΛT C L ≃ F
      ΛL≃F = generation-reff₂ Γ⊢refΛL∶F≡G in
  let ΛL≃G : ΛT C L ≃ G
      ΛL≃G = generation-reff₃ Γ⊢refΛL∶F≡G in
  let D ,p ΓC⊢L∶D ,p B⇛A≡C⇛D = generation-ΛT Γ⊢ΛL∶B⇛A in
  let B≡C : B ≡ C
      B≡C = ⇛-injl B⇛A≡C⇛D in
  let Γ⊢P∶N≡〈C〉N' : Γ ⊢ P ∶ N ≡〈 C 〉 N'
      Γ⊢P∶N≡〈C〉N' = subst (λ x → Γ ⊢ P ∶ N ≡〈 x 〉 N') B≡C Γ⊢P∶N≡N' in
  let A≡D : A ≡ D
      A≡D = ⇛-injr B⇛A≡C⇛D in
  subst (λ x → Γ ⊢ L ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧ ∶ M ≡〈 x 〉 M')
    (≡-sym A≡D) 
    (convER (path-substitution ΓC⊢L∶D (botPathSub-typed Γ⊢P∶N≡〈C〉N') 
    (botSub-typed (eq-validity₁ Γ⊢P∶N≡〈C〉N' refl)) (botSub-typed (eq-validity₂ Γ⊢P∶N≡〈C〉N' refl)) (context-validity Γ⊢refΛLP∶M≡M')) 
    (change-type (eq-validity₁ Γ⊢refΛLP∶M≡M' refl) (cong ty A≡D)) 
    (change-type (eq-validity₂ Γ⊢refΛLP∶M≡M' refl) (cong ty A≡D)) 
    (trans (trans (sym (inc βT)) (≃-appTl ΛL≃F)) FN≃M) 
    (trans (trans (sym (inc βT)) (≃-appTl ΛL≃G)) GN'≃M'))
subject-reduction-⇒ {A = app (-eq A) (φ ∷ (φ' ∷ []))} Γ⊢refM⊃*refN∶φ≡φ' ref⊃* = 
  let ψ ,p ψ' ,p χ ,p χ' ,p Γ⊢refM∶ψ≡ψ' ,p Γ⊢refN∶χ≡χ' ,p φ≃ψ⊃χ ,p φ'≃ψ'⊃χ' ,p A≡Ω 
              = generation-⊃* Γ⊢refM⊃*refN∶φ≡φ' in
  convER (refR (change-type (⊃R (generation-reff₁ Γ⊢refM∶ψ≡ψ') (generation-reff₁ Γ⊢refN∶χ≡χ')) (cong ty (≡-sym A≡Ω)))) (eq-validity₁ Γ⊢refM⊃*refN∶φ≡φ' refl) (eq-validity₂ Γ⊢refM⊃*refN∶φ≡φ' refl) 
  (sym (trans φ≃ψ⊃χ (≃-imp (sym (generation-reff₂ Γ⊢refM∶ψ≡ψ')) (sym (generation-reff₂ Γ⊢refN∶χ≡χ'))))) 
  (trans (≃-imp (generation-reff₃ Γ⊢refM∶ψ≡ψ') (generation-reff₃ Γ⊢refN∶χ≡χ')) (sym φ'≃ψ'⊃χ'))
subject-reduction-⇒ {V} {Γ = Γ} {A = app (-eq A) (M ∷ (N ∷ []))} Γ⊢refφ⊃*univδε∶M≡N (ref⊃*univ {φ = φ} {ψ} {χ} {δ} {ε}) = 
  let α ,p α' ,p β ,p β' ,p Γ⊢refφ∶α≡α' ,p Γ⊢univδε∶β≡β' ,p M≃α⊃β ,p N≃α'⊃β' ,p A≡Ω = generation-⊃* Γ⊢refφ⊃*univδε∶M≡N in
  let Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω
      Γ⊢φ∶Ω = generation-reff₁ Γ⊢refφ∶α≡α' in
  let Γ⊢δ∶ψ⊃χ : Γ ⊢ δ ∶ ψ ⊃ χ
      Γ⊢δ∶ψ⊃χ = generation-univ₃ Γ⊢univδε∶β≡β' in
  let Γ⊢ψ⊃χ∶Ω : Γ ⊢ ψ ⊃ χ ∶ ty Ω
      Γ⊢ψ⊃χ∶Ω = prop-validity Γ⊢δ∶ψ⊃χ in
  let Γ⊢ψ∶Ω : Γ ⊢ ψ ∶ ty Ω
      Γ⊢ψ∶Ω = generation-⊃₁ Γ⊢ψ⊃χ∶Ω in
  let Γ⊢φ⊃ψ∶Ω : Γ ⊢ φ ⊃ ψ ∶ ty Ω
      Γ⊢φ⊃ψ∶Ω = ⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω in
  let Γ⊢ε∶χ⊃ψ : Γ ⊢ ε ∶ χ ⊃ ψ
      Γ⊢ε∶χ⊃ψ = generation-univ₄ Γ⊢univδε∶β≡β' in
  let Γ⊢χ∶Ω : Γ ⊢ χ ∶ ty Ω
      Γ⊢χ∶Ω = generation-⊃₂ Γ⊢ψ⊃χ∶Ω in
  let validΓ,φ⊃ψ : valid (Γ ,P φ ⊃ ψ)
      validΓ,φ⊃ψ = ctxPR Γ⊢φ⊃ψ∶Ω in
  let upRepφ⊃ψ : upRep ∶ Γ ⇒R Γ ,P φ ⊃ ψ
      upRepφ⊃ψ = upRep-typed (φ ⊃ ψ) in
  let Γφ⊃ψ⊢φ∶Ω : Γ ,P φ ⊃ ψ ⊢ φ ⇑ ∶ ty Ω
      Γφ⊃ψ⊢φ∶Ω = weaken-prop Γ⊢φ∶Ω Γ⊢φ⊃ψ∶Ω in
  let validΓ,φ⊃ψ,φ : valid (Γ ,P φ ⊃ ψ ,P φ ⇑)
      validΓ,φ⊃ψ,φ = ctxPR Γφ⊃ψ⊢φ∶Ω in
  let Γ⊢φ⊃χ∶Ω : Γ ⊢ φ ⊃ χ ∶ ty Ω
      Γ⊢φ⊃χ∶Ω = ⊃R Γ⊢φ∶Ω Γ⊢χ∶Ω in
  let validΓ,φ⊃χ : valid (Γ ,P φ ⊃ χ)
      validΓ,φ⊃χ = ctxPR Γ⊢φ⊃χ∶Ω in
  let upRepφ⊃χ : upRep ∶ Γ ⇒R Γ ,P φ ⊃ χ
      upRepφ⊃χ = upRep-typed (φ ⊃ χ) in
  let Γφ⊃χ⊢φ∶Ω : Γ ,P φ ⊃ χ ⊢ φ ⇑ ∶ ty Ω
      Γφ⊃χ⊢φ∶Ω = weaken-prop Γ⊢φ∶Ω Γ⊢φ⊃χ∶Ω in
  let validΓ,φ⊃χ,φ : valid (Γ ,P φ ⊃ χ ,P φ ⇑)
      validΓ,φ⊃χ,φ = ctxPR Γφ⊃χ⊢φ∶Ω in
  subst (λ x → Γ ⊢ univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀))))) ∶ M ≡〈 x 〉 N) 
    (≡-sym A≡Ω) 
    (convER (univR (ΛPR Γ⊢φ⊃ψ∶Ω Γ⊢φ⊃χ∶Ω
    (ΛPR Γφ⊃ψ⊢φ∶Ω (weaken-prop Γ⊢χ∶Ω Γ⊢φ⊃ψ∶Ω)
    (appPR (weaken-prop₂ Γ⊢δ∶ψ⊃χ Γ⊢φ⊃ψ∶Ω Γ⊢φ∶Ω)
    (appPR (varR x₁ validΓ,φ⊃ψ,φ) (varR x₀ validΓ,φ⊃ψ,φ))))) 
    (ΛPR Γ⊢φ⊃χ∶Ω Γ⊢φ⊃ψ∶Ω 
    (ΛPR Γφ⊃χ⊢φ∶Ω (weaken-prop Γ⊢ψ∶Ω Γ⊢φ⊃χ∶Ω)
    (appPR (weaken-prop₂ Γ⊢ε∶χ⊃ψ Γ⊢φ⊃χ∶Ω Γ⊢φ∶Ω)
    (appPR (varR x₁ validΓ,φ⊃χ,φ) (varR x₀ validΓ,φ⊃χ,φ)))))) 
    (change-type (eq-validity₁ Γ⊢refφ⊃*univδε∶M≡N refl) (cong ty A≡Ω)) 
    (change-type (eq-validity₂ Γ⊢refφ⊃*univδε∶M≡N refl) (cong ty A≡Ω)) 
    (sym (trans M≃α⊃β (≃-imp (sym (generation-reff₂ Γ⊢refφ∶α≡α')) (sym (generation-univ₁ Γ⊢univδε∶β≡β'))))) 
    (trans (≃-imp (generation-reff₃ Γ⊢refφ∶α≡α') (generation-univ₂ Γ⊢univδε∶β≡β')) (sym N≃α'⊃β')))
subject-reduction-⇒ {V} {Γ = Γ} {A = app (-eq A) (M ∷ (N ∷ []))} Γ⊢univδε⊃*refχ∶M≡N (univ⊃*ref {φ = φ} {ψ} {χ} {δ} {ε}) =
  let α ,p α' ,p β ,p β' ,p Γ⊢univδε∶α≡α' ,p Γ⊢refχ∶β≡β' ,p M≃α⊃β ,p N≃α'⊃β' ,p A≡Ω = generation-⊃* Γ⊢univδε⊃*refχ∶M≡N in
  let Γ⊢φ⊃ψ∶Ω : Γ ⊢ φ ⊃ ψ ∶ ty Ω
      Γ⊢φ⊃ψ∶Ω = prop-validity (generation-univ₃ Γ⊢univδε∶α≡α') in
  let Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω
      Γ⊢φ∶Ω = generation-⊃₁ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢ψ∶Ω : Γ ⊢ ψ ∶ ty Ω
      Γ⊢ψ∶Ω = generation-⊃₂ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢χ∶Ω : Γ ⊢ χ ∶ ty Ω
      Γ⊢χ∶Ω = generation-reff₁ Γ⊢refχ∶β≡β' in
  let Γ⊢φ⊃χ∶Ω : Γ ⊢ φ ⊃ χ ∶ ty Ω
      Γ⊢φ⊃χ∶Ω = ⊃R Γ⊢φ∶Ω Γ⊢χ∶Ω in
  let Γ⊢ψ⊃χ∶Ω : Γ ⊢ ψ ⊃ χ ∶ ty Ω
      Γ⊢ψ⊃χ∶Ω = ⊃R Γ⊢ψ∶Ω Γ⊢χ∶Ω in
  let validΓ,φ⊃χ,ψ : valid (Γ ,P φ ⊃ χ ,P ψ ⇑)
      validΓ,φ⊃χ,ψ = ctxPR (weaken-prop Γ⊢ψ∶Ω Γ⊢φ⊃χ∶Ω) in
  let validΓ,ψ⊃χ,φ : valid (Γ ,P ψ ⊃ χ ,P φ ⇑)
      validΓ,ψ⊃χ,φ = ctxPR (weaken-prop Γ⊢φ∶Ω Γ⊢ψ⊃χ∶Ω) in
  subst (λ x → Γ ⊢ univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))) ∶ M ≡〈 x 〉 N) 
  (≡-sym A≡Ω) 
  (convER 
    (univR 
      (ΛPR Γ⊢φ⊃χ∶Ω Γ⊢ψ⊃χ∶Ω
      (ΛPR (weaken-prop Γ⊢ψ∶Ω Γ⊢φ⊃χ∶Ω) (weaken-prop Γ⊢χ∶Ω Γ⊢φ⊃χ∶Ω)
      (appPR (varR x₁ validΓ,φ⊃χ,ψ)
      (appPR (weaken-prop₂ (generation-univ₄ Γ⊢univδε∶α≡α') Γ⊢φ⊃χ∶Ω Γ⊢ψ∶Ω) 
      (varR x₀ validΓ,φ⊃χ,ψ))))) 
      (ΛPR Γ⊢ψ⊃χ∶Ω Γ⊢φ⊃χ∶Ω 
      (ΛPR (weaken-prop Γ⊢φ∶Ω Γ⊢ψ⊃χ∶Ω) (weaken-prop Γ⊢χ∶Ω Γ⊢ψ⊃χ∶Ω) 
      (appPR (varR x₁ validΓ,ψ⊃χ,φ)
      (appPR (weaken-prop₂ (generation-univ₃ Γ⊢univδε∶α≡α') Γ⊢ψ⊃χ∶Ω Γ⊢φ∶Ω) 
      (varR x₀ validΓ,ψ⊃χ,φ)))))) 
    (change-type (eq-validity₁ Γ⊢univδε⊃*refχ∶M≡N refl) (cong ty A≡Ω)) 
    (change-type (eq-validity₂ Γ⊢univδε⊃*refχ∶M≡N refl) (cong ty A≡Ω)) 
    (sym (trans M≃α⊃β (≃-imp (sym (generation-univ₁ Γ⊢univδε∶α≡α')) (sym (generation-reff₂ Γ⊢refχ∶β≡β'))))) 
    (trans (≃-imp (generation-univ₂ Γ⊢univδε∶α≡α') (generation-reff₃ Γ⊢refχ∶β≡β')) (sym N≃α'⊃β')))
subject-reduction-⇒ {Γ = Γ} {A = app (-eq A) (M ∷ (N ∷ []))} Γ⊢univδε⊃*univδ'ε'∶M≡N (univ⊃*univ {φ = φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'}) =
  let α ,p α' ,p β ,p β' ,p Γ⊢univδε∶α≡α' ,p Γ⊢univδ'ε'∶β≡β' ,p M≃α⊃β ,p N≃α'⊃β' ,p A≡Ω = generation-⊃* Γ⊢univδε⊃*univδ'ε'∶M≡N in 
  let Γ⊢φ⊃ψ∶Ω : Γ ⊢ φ ⊃ ψ ∶ ty Ω
      Γ⊢φ⊃ψ∶Ω = prop-validity (generation-univ₃ Γ⊢univδε∶α≡α') in
  let Γ⊢φ'⊃ψ'∶Ω : Γ ⊢ φ' ⊃ ψ' ∶ ty Ω
      Γ⊢φ'⊃ψ'∶Ω = prop-validity (generation-univ₃ Γ⊢univδ'ε'∶β≡β') in
  let Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω
      Γ⊢φ∶Ω = generation-⊃₁ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢ψ∶Ω : Γ ⊢ ψ ∶ ty Ω
      Γ⊢ψ∶Ω = generation-⊃₂ Γ⊢φ⊃ψ∶Ω in
  let Γ⊢φ'∶Ω : Γ ⊢ φ' ∶ ty Ω
      Γ⊢φ'∶Ω = generation-⊃₁ Γ⊢φ'⊃ψ'∶Ω in
  let Γ⊢ψ'∶Ω : Γ ⊢ ψ' ∶ ty Ω
      Γ⊢ψ'∶Ω = generation-⊃₂ Γ⊢φ'⊃ψ'∶Ω in
  let Γ⊢φ⊃φ'∶Ω : Γ ⊢ φ ⊃ φ' ∶ ty Ω
      Γ⊢φ⊃φ'∶Ω = ⊃R Γ⊢φ∶Ω Γ⊢φ'∶Ω in
  let Γ⊢ψ⊃ψ'∶Ω : Γ ⊢ ψ ⊃ ψ' ∶ ty Ω
      Γ⊢ψ⊃ψ'∶Ω = ⊃R Γ⊢ψ∶Ω Γ⊢ψ'∶Ω in
  let validΓ,φ⊃φ',ψ : valid (Γ ,P φ ⊃ φ' ,P ψ ⇑)
      validΓ,φ⊃φ',ψ = ctxPR (weaken-prop Γ⊢ψ∶Ω Γ⊢φ⊃φ'∶Ω) in
  subst
    (λ x →
       Γ ⊢
       univ (φ ⊃ φ') (ψ ⊃ ψ')
       (ΛP (φ ⊃ φ')
        (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))))
       (ΛP (ψ ⊃ ψ')
        (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
       ∶ M ≡〈 x 〉 N)
    (≡-sym A≡Ω) 
  (convER 
    (univR 
      (ΛPR Γ⊢φ⊃φ'∶Ω Γ⊢ψ⊃ψ'∶Ω 
      (ΛPR (weaken-prop Γ⊢ψ∶Ω Γ⊢φ⊃φ'∶Ω) (weaken-prop Γ⊢ψ'∶Ω Γ⊢φ⊃φ'∶Ω) 
      (appPR (weaken-prop₂ (generation-univ₃ Γ⊢univδ'ε'∶β≡β') Γ⊢φ⊃φ'∶Ω Γ⊢ψ∶Ω) 
      (appPR (varR x₁ validΓ,φ⊃φ',ψ) 
      (appPR (weaken-prop₂ (generation-univ₄ Γ⊢univδε∶α≡α') Γ⊢φ⊃φ'∶Ω Γ⊢ψ∶Ω) 
      (varR x₀ validΓ,φ⊃φ',ψ)))))) 
      (ΛPR Γ⊢ψ⊃ψ'∶Ω Γ⊢φ⊃φ'∶Ω 
      (ΛPR (weaken-prop Γ⊢φ∶Ω Γ⊢ψ⊃ψ'∶Ω) (weaken-prop Γ⊢φ'∶Ω Γ⊢ψ⊃ψ'∶Ω) 
      (appPR (weaken-prop₂ (generation-univ₄ Γ⊢univδ'ε'∶β≡β') Γ⊢ψ⊃ψ'∶Ω Γ⊢φ∶Ω) 
      (appPR (varR x₁ (ctxPR (weaken-prop Γ⊢φ∶Ω Γ⊢ψ⊃ψ'∶Ω))) 
      (appPR (weaken-prop₂ (generation-univ₃ Γ⊢univδε∶α≡α') Γ⊢ψ⊃ψ'∶Ω Γ⊢φ∶Ω) 
      (varR x₀ (ctxPR (weaken-prop Γ⊢φ∶Ω Γ⊢ψ⊃ψ'∶Ω))))))))) 
    (change-type (eq-validity₁ Γ⊢univδε⊃*univδ'ε'∶M≡N refl) (cong ty A≡Ω)) 
    (change-type (eq-validity₂ Γ⊢univδε⊃*univδ'ε'∶M≡N refl) (cong ty A≡Ω)) 
    (trans (≃-imp (generation-univ₁ Γ⊢univδε∶α≡α') (generation-univ₁ Γ⊢univδ'ε'∶β≡β')) (sym M≃α⊃β)) 
    (trans (≃-imp (generation-univ₂ Γ⊢univδε∶α≡α') (generation-univ₂ Γ⊢univδ'ε'∶β≡β')) (sym N≃α'⊃β')))
subject-reduction-⇒ {Γ = Γ} {A = app (-eq A) (M ∷ (N ∷ []))} Γ⊢P⊃*Q∶M≡N (imp*l {P = P} {P' = P'} {Q = Q} P⇒P') = 
  let φ ,p φ' ,p ψ ,p ψ' ,p Γ⊢P∶φ≡φ' ,p Γ⊢Q∶ψ≡ψ' ,p M≃φ⊃ψ ,p N≃φ'⊃ψ' ,p A≡Ω = generation-⊃* Γ⊢P⊃*Q∶M≡N in 
  subst (λ x → Γ ⊢ P' ⊃* Q ∶ M ≡〈 x 〉 N) (≡-sym A≡Ω) (convER (⊃*R (subject-reduction-⇒ Γ⊢P∶φ≡φ' P⇒P') Γ⊢Q∶ψ≡ψ') 
    (change-type (eq-validity₁ Γ⊢P⊃*Q∶M≡N refl) (cong ty A≡Ω)) 
    (change-type (eq-validity₂ Γ⊢P⊃*Q∶M≡N refl) (cong ty A≡Ω)) 
    (sym M≃φ⊃ψ) (sym N≃φ'⊃ψ'))
subject-reduction-⇒ {Γ = Γ} {A = app (-eq A) (M ∷ (N ∷ []))} Γ⊢P⊃*Q∶M≡N (imp*r {P = P} {Q} {Q'} Q⇒Q') =
  let φ ,p φ' ,p ψ ,p ψ' ,p Γ⊢P∶φ≡φ' ,p Γ⊢Q∶ψ≡ψ' ,p M≃φ⊃ψ ,p N≃φ'⊃ψ' ,p A≡Ω = generation-⊃* Γ⊢P⊃*Q∶M≡N in
  subst (λ x → Γ ⊢ P ⊃* Q' ∶ M ≡〈 x 〉 N) (≡-sym A≡Ω) (convER (⊃*R Γ⊢P∶φ≡φ' (subject-reduction-⇒ Γ⊢Q∶ψ≡ψ' Q⇒Q')) 
  (change-type (eq-validity₁ Γ⊢P⊃*Q∶M≡N refl) (cong ty A≡Ω)) 
  (change-type (eq-validity₂ Γ⊢P⊃*Q∶M≡N refl) (cong ty A≡Ω)) 
  (sym M≃φ⊃ψ) (sym N≃φ'⊃ψ'))
subject-reduction-⇒ {Γ = Γ} {A = app (-eq A) (L ∷ (L' ∷ []))} Γ⊢PQ∶L≡L' (app*l {M = M} {N} {P = P} {P'} {Q} P⇒P') = 
  let B ,p F ,p G ,p Γ⊢P∶F≡G ,p Γ⊢Q∶M≡N ,p FM≃L ,p GN≃L' = generation-app* Γ⊢PQ∶L≡L' in
  convER (appER (eq-validity₁ Γ⊢Q∶M≡N refl) (eq-validity₂ Γ⊢Q∶M≡N refl) (subject-reduction-⇒ Γ⊢P∶F≡G P⇒P') Γ⊢Q∶M≡N) (eq-validity₁ Γ⊢PQ∶L≡L' refl) (eq-validity₂ Γ⊢PQ∶L≡L' refl) 
  FM≃L GN≃L'
subject-reduction-⇒ {A = app (-eq A) (L ∷ (L' ∷ []))} Γ⊢refMQ∶L≡L' (reffR M⇒M') =
  let B ,p F ,p G ,p Γ⊢refM∶F≡G ,p Γ⊢Q∶N≡N' ,p FM≃L ,p GN≃L' = generation-app* Γ⊢refMQ∶L≡L' in 
  convER 
    (appER (eq-validity₁ Γ⊢Q∶N≡N' refl) (eq-validity₂ Γ⊢Q∶N≡N' refl) 
      (refR (subject-reduction-⇒ (generation-reff₁ Γ⊢refM∶F≡G) M⇒M')) 
      Γ⊢Q∶N≡N') 
    (eq-validity₁ Γ⊢refMQ∶L≡L' refl) (eq-validity₂ Γ⊢refMQ∶L≡L' refl) 
  (trans (≃-appTl (trans (sym (inc M⇒M')) (generation-reff₂ Γ⊢refM∶F≡G))) FM≃L) 
  (trans (≃-appTl (trans (sym (inc M⇒M')) (generation-reff₃ Γ⊢refM∶F≡G))) GN≃L')

subject-reduction : ∀ {V} {K} {Γ} {E F : Expression V (varKind K)} {A} → (Γ ⊢ E ∶ A) → (E ↠ F) → (Γ ⊢ F ∶ A)
subject-reduction Γ⊢E∶A (inc E⇒F) = subject-reduction-⇒ Γ⊢E∶A E⇒F
subject-reduction Γ⊢E∶A ref = Γ⊢E∶A
subject-reduction Γ⊢E∶A (trans E↠F F↠G) = subject-reduction (subject-reduction Γ⊢E∶A E↠F) F↠G
