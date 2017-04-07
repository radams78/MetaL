module PHOML.MainTheorem where
open import Data.List
open import Data.Product hiding (_,_)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Rules
open import PHOML.Canon
open import PHOML.Compute
open import PHOML.Lemma35
open import PHOML.ComputeSub

soundness : ∀ {U V} {Γ : Context U} {K} {E : VExpression U K} {T} {σ : Sub U V} → 
  Γ ⊢ E ∶ T → ⊧S σ ∶ Γ → ⊧ E ⟦ σ ⟧ ∶ T ⟦ σ ⟧
soundness-path : ∀ {U V} {Γ : Context U} {M A} {τ : PathSub U V} {ρ σ} →
  Γ ⊢ M ∶ A → ⊧S ρ ∶ Γ → ⊧S σ ∶ Γ → ⊧ τ ∶ ρ ≡ σ ∶ Γ → ⊧E M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧

soundness (varR x _) ⊧Sσ∶Γ = ⊧Sσ∶Γ x
soundness (appTR Γ⊢M∶A⇛B Γ⊢M∶A) ⊧Sσ∶Γ = ⊧appT (soundness Γ⊢M∶A⇛B ⊧Sσ∶Γ) (soundness Γ⊢M∶A ⊧Sσ∶Γ)
soundness {U} {V} {σ = σ} (ΛTR {A = A} {M = M} {B} Γ,A⊢M∶B) ⊧Sσ∶Γ W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' =
  let NN'Q : Sub (extend W pathDom) W
      NN'Q = x₂:= N ,x₁:= N' ,x₀:= Q in
  let σ↑ : Sub (U , -Term) (W , -Term)
      σ↑ = liftSub -Term (ρ •RS σ) in
  let σ↑N : Sub (U , -Term) W
      σ↑N = x₀:= N • σ↑ in
  let σ↑N' : Sub (U , -Term) W
      σ↑N' = x₀:= N' • σ↑ in
  let ⊧MσQ∶MN≡MN' : ⊧E M ⟦⟦ x₀::= Q ∶ x₀:= N ≡ x₀:= N' •PS σ↑ ∶ σ↑N ≡ σ↑N' ⟧⟧ ∶ M ⟦ σ↑N ⟧ ≡〈 B 〉 M ⟦ σ↑N' ⟧
      ⊧MσQ∶MN≡MN' = soundness-path Γ,A⊢M∶B (⊧extendSub' (⊧RS ⊧Sσ∶Γ) ⊧N∶A) 
        (⊧extendSub' (⊧RS ⊧Sσ∶Γ) ⊧N'∶A) (⊧extend (⊧RS ⊧Sσ∶Γ) ⊧Q∶N≡N') in
  let ⊧MrQ∶MN≡MN' : ⊧E M ⟦ σ↑ ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ NN'Q ⟧ ∶ M ⟦ σ↑N ⟧ ≡〈 B 〉 M ⟦ σ↑N' ⟧
      ⊧MrQ∶MN≡MN' = subst (λ x → ⊧E x ∶ M ⟦ σ↑N ⟧ ≡〈 B 〉 (M ⟦ σ↑N' ⟧)) (let open ≡-Reasoning in 
        begin
          M ⟦⟦ x₀::= Q ∶ x₀:= N ≡ x₀:= N' •PS σ↑ ∶ σ↑N ≡ σ↑N' ⟧⟧
        ≡⟨ pathSub-cong M (•PS-congl {ρ = liftSub -Term (ρ •RS σ)} (∼∼-sym botSub₃-liftRefSub) (sub-sym botSub₃-sub↖id) (sub-sym botSub₃-sub↗id)) 
           (•-congl (sub-sym botSub₃-sub↖id) (liftSub -Term (ρ •RS σ))) (•-congl (sub-sym botSub₃-sub↗id) (liftSub -Term (ρ •RS σ))) ⟩
          M ⟦⟦ NN'Q •SP liftPathSub refSub ∶ NN'Q • sub↖ (idSub W) ≡ NN'Q • sub↗ (idSub W) •PS σ↑ ∶ (NN'Q • sub↖ (idSub W)) • σ↑ ≡ (NN'Q • sub↗ (idSub W)) • σ↑ ⟧⟧
        ≡⟨ pathSub-•PS M ⟩
          M ⟦ σ↑ ⟧ ⟦⟦ NN'Q •SP liftPathSub refSub ∶ NN'Q • sub↖ (idSub W) ≡ NN'Q • sub↗ (idSub W) ⟧⟧
        ≡⟨ pathSub-•SP (M ⟦ σ↑ ⟧) ⟩
          M ⟦ σ↑ ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
        ∎) 
        ⊧MσQ∶MN≡MN' in 
  expansionE (conversionE ⊧MrQ∶MN≡MN' 
    (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      M ⟦ x₀:= N • liftSub -Term (ρ •RS σ) ⟧
    ≡⟨ sub-• M ⟩
      M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
    ≡⟨ sub-congl (liftSub-•RS M) ⟩
      M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N ⟧
    ≈⟨⟨ inc βT ⟩⟩
      appT (ΛT A (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉)) N
    ∎) 
    (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      M ⟦ x₀:= N' • liftSub -Term (ρ •RS σ) ⟧
    ≡⟨ sub-• M ⟩
      M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦ x₀:= N' ⟧
    ≡⟨ sub-congl (liftSub-•RS M) ⟩
      M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N' ⟧
    ≈⟨⟨ inc βT ⟩⟩
      appT (ΛT A (M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉)) N'
    ∎)) 
    (subst
       (λ x →
          app* N N'
          (λλλ A
           ((M ⟦ liftSub -Term σ ⟧) ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡
            sub↗ (idSub V) ⟧⟧)
           〈 ρ 〉)
          Q
          ⇒ x)
     (let open ≡-Reasoning in 
     begin
       M ⟦ liftSub -Term σ ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ sub-congl (pathSub-•RP (M ⟦ liftSub -Term σ ⟧)) ⟩⟩
       M ⟦ liftSub -Term σ ⟧ ⟦⟦ liftsRep pathDom ρ •RP liftPathSub refSub ∶ liftsRep pathDom ρ •RS sub↖ (idSub V) ≡ liftsRep pathDom ρ •RS sub↗ (idSub V) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨ sub-congl (pathSub-cong (M ⟦ liftSub -Term σ ⟧) 
        liftsRep-liftRefSub 
        liftsRep-sub↖id 
        liftsRep-sub↗id) ⟩
       M ⟦ liftSub -Term σ ⟧ ⟦⟦ liftPathSub refSub •PR liftRep -Term ρ ∶ sub↖ (idSub W) •SR liftRep -Term ρ ≡ sub↗ (idSub W) •SR liftRep -Term ρ ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ sub-congl (pathSub-•PR (M ⟦ liftSub -Term σ ⟧)) ⟩⟩
       M ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term ρ 〉 ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ≡⟨⟨ cong
          (λ x →
             (x ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧) ⟦
             x₂:= N ,x₁:= N' ,x₀:= Q ⟧)
          (liftSub-•RS M) ⟩⟩
       M ⟦ liftSub -Term (ρ •RS σ) ⟧ ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub W) ≡ sub↗ (idSub W) ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
     ∎) 
    βE)
soundness (⊥R validΓ) ⊧Sσ∶Γ = ⊧canon' bot ref
soundness (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) ⊧Sσ∶Γ = ⊧imp (soundness Γ⊢φ∶Ω ⊧Sσ∶Γ) (soundness Γ⊢ψ∶Ω ⊧Sσ∶Γ)
soundness (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) ⊧Sσ∶Γ = ⊧P⊃E (soundness Γ⊢δ∶φ⊃ψ ⊧Sσ∶Γ) (soundness Γ⊢ε∶φ ⊧Sσ∶Γ)
soundness {U} {σ = σ} (ΛPR {δ = δ} {φ = φ} {ψ = ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ψ) ⊧Sσ∶Γ = ⊧P⊃I (soundness Γ⊢φ∶Ω ⊧Sσ∶Γ) (soundness Γ⊢ψ∶Ω ⊧Sσ∶Γ) 
  (λ W ρ ε ⊧ε∶φ →
    let σε : Sub (U , -Proof) W
        σε = extendSub (ρ •RS σ) ε in
    let ⊧δε∶ψ : ⊧P δ ⟦ σε ⟧ ∶ ψ ⇑ ⟦ σε ⟧
        ⊧δε∶ψ = soundness Γ,φ⊢δ∶ψ (⊧extendSub (⊧RS ⊧Sσ∶Γ) (⊧P-change-prop ⊧ε∶φ (≡-sym (sub-•RS φ)))) in
    let ⊧δε∶ψ₂ : ⊧P δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧ ∶ ψ ⟦ σ ⟧ 〈 ρ 〉
        ⊧δε∶ψ₂ = subst₂ ⊧P_∶_ 
          (let open ≡-Reasoning in 
          begin
            δ ⟦ extendSub (ρ •RS σ) ε ⟧
          ≡⟨ extendSub-decomp δ ⟩
            δ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= ε ⟧
          ≡⟨ sub-congl (liftSub-•RS δ) ⟩
            δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧
          ∎) 
          (let open ≡-Reasoning in
          begin
            ψ ⇑ ⟦ extendSub (ρ •RS σ) ε ⟧
          ≡⟨ extendSub-decomp (ψ ⇑) ⟩
            ψ ⇑ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= ε ⟧
          ≡⟨ sub-congl (liftSub-upRep ψ) ⟩
            ψ ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= ε ⟧
          ≡⟨ botSub-upRep (ψ ⟦ ρ •RS σ ⟧) ⟩
            ψ ⟦ ρ •RS σ ⟧
          ≡⟨ sub-•RS ψ ⟩
            ψ ⟦ σ ⟧ 〈 ρ 〉
          ∎) ⊧δε∶ψ in
    expansionP ⊧δε∶ψ₂ βP)
soundness (convPR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) ⊧Sσ∶Γ = conversionP (soundness Γ⊢δ∶φ ⊧Sσ∶Γ) (≃-resp-sub φ≃ψ)
soundness (refR Γ⊢M∶A) ⊧Sσ∶Γ = ⊧ref (soundness Γ⊢M∶A ⊧Sσ∶Γ)
soundness (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') ⊧Sσ∶Γ = ⊧⊃* (soundness Γ⊢P∶φ≡φ' ⊧Sσ∶Γ) (soundness Γ⊢Q∶ψ≡ψ' ⊧Sσ∶Γ)
soundness (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) ⊧Sσ∶Γ = ⊧univ (soundness Γ⊢δ∶φ⊃ψ ⊧Sσ∶Γ) (soundness Γ⊢ε∶ψ⊃φ ⊧Sσ∶Γ)
soundness (plusR Γ⊢P∶φ≡ψ) ⊧Sσ∶Γ = proj₁ (soundness Γ⊢P∶φ≡ψ ⊧Sσ∶Γ)
soundness (minusR Γ⊢P∶φ≡ψ) ⊧Sσ∶Γ = proj₂ (soundness Γ⊢P∶φ≡ψ ⊧Sσ∶Γ)
soundness {U} {σ = σ} (lllR {B = B} {M = F} {G} {P} _ _ ΓAAE⊢P∶Fx≡Gy) ⊧Sσ∶Γ W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = 
  let σ' : Sub (extend U pathDom) W
      σ' = extendSub (extendSub (extendSub (ρ •RS σ) N) N') Q in
  let PQ∶FN≡GN' : ⊧E P ⟦ σ' ⟧ ∶ appT (F ⇑ ⇑ ⇑ ⟦ σ' ⟧) N ≡〈 B 〉 appT (G ⇑ ⇑ ⇑ ⟦ σ' ⟧) N'
      PQ∶FN≡GN' = soundness ΓAAE⊢P∶Fx≡Gy (⊧extendSub (⊧extendSub (⊧extendSub (⊧RS ⊧Sσ∶Γ) ⊧N∶A) ⊧N'∶A) ⊧Q∶N≡N') in
  let PQ∶FN≡GN'₂ : ⊧E P ⟦ liftsSub pathDom σ ⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧ ∶ appT (F ⟦ σ ⟧ 〈 ρ 〉) N ≡〈 B 〉 appT (G ⟦ σ ⟧ 〈 ρ 〉) N'
      PQ∶FN≡GN'₂ = subst₃ (λ x₃ y z → ⊧E x₃ ∶ y ≡〈 B 〉 z) 
        (let open ≡-Reasoning in 
        begin
          P ⟦ σ' ⟧
        ≡⟨ sub-congr P subeq ⟩
          P ⟦ (x₂:= N ,x₁:= N' ,x₀:= Q) • (liftsRep pathDom ρ •RS liftsSub pathDom σ) ⟧
        ≡⟨ sub-• P ⟩
          P ⟦ liftsRep pathDom ρ •RS liftsSub pathDom σ ⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
        ≡⟨ sub-congl (sub-•RS P) ⟩
          P ⟦ liftsSub pathDom σ ⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
        ∎) 
        (cong (λ x → appT x N) (let open ≡-Reasoning in 
        begin
          F ⇑ ⇑ ⇑ ⟦ σ' ⟧
        ≡⟨ extendSub-decomp (F ⇑ ⇑ ⇑) ⟩
          F ⇑ ⇑ ⇑ ⟦ liftSub _ (extendSub (extendSub (ρ •RS σ) N) N') ⟧ ⟦ x₀:= Q ⟧
        ≡⟨ sub-congl (liftSub-upRep (F ⇑ ⇑)) ⟩
          F ⇑ ⇑ ⟦ extendSub (extendSub (ρ •RS σ) N) N' ⟧ ⇑ ⟦ x₀:= Q ⟧
        ≡⟨ botSub-upRep (F ⇑ ⇑ ⟦ extendSub (extendSub (ρ •RS σ) N) N' ⟧) ⟩
          F ⇑ ⇑ ⟦ extendSub (extendSub (ρ •RS σ) N) N' ⟧
        ≡⟨ extendSub-decomp (F ⇑ ⇑) ⟩
          F ⇑ ⇑ ⟦ liftSub _ (extendSub (ρ •RS σ) N) ⟧ ⟦ x₀:= N' ⟧
        ≡⟨ sub-congl (liftSub-upRep (F ⇑)) ⟩
          F ⇑ ⟦ extendSub (ρ •RS σ) N ⟧ ⇑ ⟦ x₀:= N' ⟧
        ≡⟨ botSub-upRep (F ⇑ ⟦ extendSub (ρ •RS σ) N ⟧) ⟩
          F ⇑ ⟦ extendSub (ρ •RS σ) N ⟧
        ≡⟨ extendSub-decomp (F ⇑) ⟩
          F ⇑ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
        ≡⟨ sub-congl (liftSub-upRep F) ⟩
          F ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= N ⟧
        ≡⟨ botSub-upRep (F ⟦ ρ •RS σ ⟧) ⟩
          F ⟦ ρ •RS σ ⟧
        ≡⟨ sub-•RS F ⟩
          F ⟦ σ ⟧ 〈 ρ 〉
        ∎)) 
        (cong (λ x → appT x N') (let open ≡-Reasoning in 
        begin
          G ⇑ ⇑ ⇑ ⟦ σ' ⟧
        ≡⟨ extendSub-decomp (G ⇑ ⇑ ⇑) ⟩
          G ⇑ ⇑ ⇑ ⟦ liftSub _ (extendSub (extendSub (ρ •RS σ) N) N') ⟧ ⟦ x₀:= Q ⟧
        ≡⟨ sub-congl (liftSub-upRep (G ⇑ ⇑)) ⟩
          G ⇑ ⇑ ⟦ extendSub (extendSub (ρ •RS σ) N) N' ⟧ ⇑ ⟦ x₀:= Q ⟧
        ≡⟨ botSub-upRep (G ⇑ ⇑ ⟦ extendSub (extendSub (ρ •RS σ) N) N' ⟧) ⟩
          G ⇑ ⇑ ⟦ extendSub (extendSub (ρ •RS σ) N) N' ⟧
        ≡⟨ extendSub-decomp (G ⇑ ⇑) ⟩
          G ⇑ ⇑ ⟦ liftSub _ (extendSub (ρ •RS σ) N) ⟧ ⟦ x₀:= N' ⟧
        ≡⟨ sub-congl (liftSub-upRep (G ⇑)) ⟩
          G ⇑ ⟦ extendSub (ρ •RS σ) N ⟧ ⇑ ⟦ x₀:= N' ⟧
        ≡⟨ botSub-upRep (G ⇑ ⟦ extendSub (ρ •RS σ) N ⟧) ⟩
          G ⇑ ⟦ extendSub (ρ •RS σ) N ⟧
        ≡⟨ extendSub-decomp (G ⇑) ⟩
          G ⇑ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
        ≡⟨ sub-congl (liftSub-upRep G) ⟩
          G ⟦ ρ •RS σ ⟧ ⇑ ⟦ x₀:= N ⟧
        ≡⟨ botSub-upRep (G ⟦ ρ •RS σ ⟧) ⟩
          G ⟦ ρ •RS σ ⟧
        ≡⟨ sub-•RS G ⟩
          G ⟦ σ ⟧ 〈 ρ 〉
        ∎)) 
        PQ∶FN≡GN' in
  expansionE PQ∶FN≡GN'₂ βE where
  subeq : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} {N N' Q} →
    extendSub (extendSub (extendSub (ρ •RS σ) N) N') Q ∼ (x₂:= N ,x₁:= N' ,x₀:= Q) • (liftsRep pathDom ρ •RS liftsSub pathDom σ)
  subeq x₀ = refl
  subeq (↑ x₀) = refl
  subeq (↑ (↑ x₀)) = refl
  subeq {ρ = ρ} {σ} {N} {N'} {Q} (↑ (↑ (↑ x))) = let open ≡-Reasoning in
    begin
      σ _ x 〈 ρ 〉
    ≡⟨⟨ botSub-upRep₃ ⟩⟩
      σ _ x 〈 ρ 〉 ⇑ ⇑ ⇑ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
    ≡⟨⟨ sub-congl (liftRep-upRep₃ (σ _ x)) ⟩⟩
      σ _ x ⇑ ⇑ ⇑ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
    ∎
soundness {U} {V} {σ = σ} (appER {P = P} {Q} {M} {M'} {N} {N'} {A} {B} Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') ⊧Sσ∶Γ = 
  subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) (cong (λ x → app* (N ⟦ σ ⟧) (N' ⟦ σ ⟧) x (Q ⟦ σ ⟧)) rep-idRep) 
    (cong (λ x → appT x (N ⟦ σ ⟧)) rep-idRep) (cong (λ x → appT x (N' ⟦ σ ⟧)) rep-idRep)
  (soundness Γ⊢P∶M≡M' ⊧Sσ∶Γ V (idRep V) (N ⟦ σ ⟧) (N' ⟦ σ ⟧) (Q ⟦ σ ⟧) 
    (soundness Γ⊢N∶A ⊧Sσ∶Γ) (soundness Γ⊢N'∶A ⊧Sσ∶Γ) (soundness Γ⊢Q∶N≡N' ⊧Sσ∶Γ))
soundness (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') ⊧Sσ∶Γ = conversionE (soundness Γ⊢P∶M≡N ⊧Sσ∶Γ) (≃-resp-sub M≃M') (≃-resp-sub N≃N')

soundness-path (varR x _ ) _ _ ⊧τ∶ρ≡σ = ⊧τ∶ρ≡σ x
soundness-path {V = V} {τ = τ} {ρ = ρ} {σ} (appTR {M = M} {N} {A} {B} Γ⊢M∶A⇛B Γ⊢N∶A) ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ = 
  subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) 
  (cong (λ x → app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) x (N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧)) rep-idRep) 
  (cong (λ x → appT x (N ⟦ ρ ⟧)) rep-idRep) 
  (cong (λ x → appT x (N ⟦ σ ⟧)) rep-idRep) 
  (soundness-path Γ⊢M∶A⇛B ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ V (idRep V) (N ⟦ ρ ⟧) (N ⟦ σ ⟧) 
    (N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧) (soundness Γ⊢N∶A ⊧ρ∶Γ) (soundness Γ⊢N∶A ⊧σ∶Γ) 
    (soundness-path Γ⊢N∶A ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ))
soundness-path {U} {V} {τ = τ} {σ} {σ'} (ΛTR {A = A} {M} {B} Γ,A⊢M∶B) ⊧σ∶Γ ⊧σ'∶Γ ⊧τ∶σ≡σ' W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = 
  let ⊧MQ∶MN≡MN' : ⊧E M ⟦⟦ extendPS (ρ •RP τ) Q ∶ extendSub (ρ •RS σ) N ≡ extendSub (ρ •RS σ') N' ⟧⟧ ∶ M ⟦ extendSub (ρ •RS σ) N ⟧ ≡〈 B 〉 M ⟦ extendSub (ρ •RS σ') N' ⟧
      ⊧MQ∶MN≡MN' = soundness-path Γ,A⊢M∶B (⊧extendSub (⊧RS ⊧σ∶Γ) ⊧N∶A) (⊧extendSub (⊧RS ⊧σ'∶Γ) ⊧N'∶A) (⊧extendPS (⊧RP {ρ = ρ} {τ} {σ} {σ'} ⊧τ∶σ≡σ') ⊧Q∶N≡N') in
  expansionE (conversionE ⊧MQ∶MN≡MN' 
    (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      M ⟦ extendSub (ρ •RS σ) N ⟧
    ≡⟨ extendSub-decomp M ⟩
      M ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= N ⟧
    ≡⟨ sub-congl (liftSub-•RS M) ⟩
      M ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N ⟧
    ≈⟨⟨ inc βT ⟩⟩
      appT (ΛT A M ⟦ σ ⟧ 〈 ρ 〉) N
    ∎) 
    (let open EqReasoning (RSTCLOSE _⇒_) in 
    begin
      M ⟦ extendSub (ρ •RS σ') N' ⟧
    ≡⟨ extendSub-decomp M ⟩
      M ⟦ liftSub _ (ρ •RS σ') ⟧ ⟦ x₀:= N' ⟧
    ≡⟨ sub-congl (liftSub-•RS M) ⟩
      M ⟦ liftSub _ σ' ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= N' ⟧
    ≈⟨⟨ inc βT ⟩⟩
      appT (ΛT A M ⟦ σ' ⟧ 〈 ρ 〉) N'
    ∎))
    (subst
       (λ x →
          app* N N' (λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ σ ≡ sub↗ σ' ⟧⟧) 〈 ρ 〉)
          Q
          ⇒ x)
    (let open ≡-Reasoning in 
    begin
      M ⟦⟦ liftPathSub τ ∶ sub↖ σ ≡ sub↗ σ' ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
    ≡⟨⟨ sub-congl (pathSub-•RP M) ⟩⟩
      M ⟦⟦ liftsRep pathDom ρ •RP liftPathSub τ ∶ liftsRep pathDom ρ •RS sub↖ σ ≡ liftsRep pathDom ρ •RS sub↗ σ' ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
    ≡⟨ sub-congl (pathSub-cong M (∼∼-sym liftPathSub-•RP) liftsRep-sub↖ liftsRep-sub↗) ⟩
      M ⟦⟦ liftPathSub (ρ •RP τ) ∶ sub↖ (ρ •RS σ) ≡ sub↗ (ρ •RS σ') ⟧⟧ ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
    ≡⟨⟨ pathSub-•SP M ⟩⟩
      M ⟦⟦ (x₂:= N ,x₁:= N' ,x₀:= Q) •SP liftPathSub (ρ •RP τ) ∶ 
           (x₂:= N ,x₁:= N' ,x₀:= Q) • sub↖ (ρ •RS σ) ≡ 
           (x₂:= N ,x₁:= N' ,x₀:= Q) • sub↗ (ρ •RS σ') ⟧⟧
    ≡⟨ pathSub-cong M botSub₃-liftPathSub botSub₃-sub↖ botSub₃-sub↗ ⟩
      M ⟦⟦ extendPS (ρ •RP τ) Q ∶ extendSub (ρ •RS σ) N ≡ extendSub (ρ •RS σ') N' ⟧⟧
    ∎) 
    βE)
soundness-path (⊥R validΓ) ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ = ⊧canon' bot ref
soundness-path (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ = ⊧⊃* (soundness-path Γ⊢φ∶Ω ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ) (soundness-path Γ⊢ψ∶Ω ⊧ρ∶Γ ⊧σ∶Γ ⊧τ∶ρ≡σ)
