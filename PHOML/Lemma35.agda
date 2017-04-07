module PHOML.Lemma35 where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Neutral
open import PHOML.Canon
open import PHOML.Compute

Pdirlm : ∀ {U V} {P : Path U} {ρ : Rep U V} {M} {δ d} → P ↠ reff M → appP (dir d P 〈 ρ 〉) δ ↠ δ
Pdirlm P↠refM = trans (↠-appP (↠-dir (↠-resp-rep P↠refM))) (trans (inc (appPl refdir)) (inc βP))

⊧⊃* : ∀ {V} {P : Path V} {φ φ' Q ψ ψ'} →
  ⊧E P ∶ φ ≡〈 Ω 〉 φ' → ⊧E Q ∶ ψ ≡〈 Ω 〉 ψ' → ⊧E P ⊃* Q ∶ φ ⊃ ψ ≡〈 Ω 〉 φ' ⊃ ψ'
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) with Lemma35e ⊧P+∶φ⊃φ'
⊧⊃* (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | Pcanon ,p P↠Pcanon with Lemma35e ⊧Q+∶ψ⊃ψ'
⊧⊃* {Q = Q} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | neutral Pcanon ,p P↠Pcanon | Qcanon ,p Q↠Qcanon = 
  ↞E (⊧neutralE {P = imp*l Pcanon Q} (⊧imp (⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ))) 
  (⊧imp (⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)))) (↠-imp*l P↠Pcanon)
⊧⊃* {P = P} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | Pcanon ,p P↠Pcanon | neutral Qcanon ,p Q↠Qcanon = 
  ↞E (⊧neutralE {P = imp*r P Qcanon} (⊧imp (⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ))) 
  (⊧imp (⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ)) (⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ)))) (↠-imp*r Q↠Qcanon)
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠refM | reffC N ,p Q↠refN = 
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ ε ⊧ε∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ ε₁ ⊧ε₁∶φ' → 
  let ⊧P-ε₁∶φ : ⊧P appP (minus P 〈 ρ₁ •R ρ 〉) ε₁ ∶ φ 〈 ρ₁ •R ρ 〉
      ⊧P-ε₁∶φ = ⊧P⊃E (⊧Prep ⊧P-∶φ'⊃φ) (⊧P-change-prop ⊧ε₁∶φ' (≡-sym (rep-•R φ'))) in
  let ⊧ε₁∶φ : ⊧P ε₁ ∶ φ 〈 ρ₁ •R ρ 〉
      ⊧ε₁∶φ = ↠P ⊧P-ε₁∶φ (Pdirlm P↠refM) in
  let ⊧εε₁∶ψ : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ = ⊧P⊃E (⊧P-change-prop (⊧Prep ⊧ε∶φ⊃ψ) (≡-sym (rep-•R (φ ⊃ ψ)))) ⊧ε₁∶φ in
  let ⊧Q+εε₁∶ψ' : ⊧P appP (plus Q 〈 ρ₁ •R ρ 〉) (appP (ε 〈 ρ₁ 〉) ε₁) ∶ ψ' 〈 ρ₁ •R ρ 〉
      ⊧Q+εε₁∶ψ' = ⊧P⊃E (⊧Prep ⊧Q+∶ψ⊃ψ') ⊧εε₁∶ψ in
  let ⊧εε₁∶ψ' : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ' 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ' = ↠P ⊧Q+εε₁∶ψ' (Pdirlm Q↠refN) in
  ↞P (⊧P-change-prop ⊧εε₁∶ψ' (rep-•R ψ')) (↠-appP (subst (λ x → appP x (ε 〈 ρ₁ 〉) ↠ ε 〈 ρ₁ 〉) (rep-•R (plus (P ⊃* Q))) (Pdirlm (trans (↠-imp* P↠refM Q↠refN) (inc ref⊃*)))))))) ,p
  (⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ ε ⊧ε∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ ε₁ ⊧ε₁∶φ → 
  let ⊧P+ε₁∶φ' : ⊧P appP (plus P 〈 ρ₁ •R ρ 〉) ε₁ ∶ φ' 〈 ρ₁ •R ρ 〉
      ⊧P+ε₁∶φ' = ⊧P⊃E (⊧Prep ⊧P+∶φ⊃φ') (⊧P-change-prop ⊧ε₁∶φ (≡-sym (rep-•R φ))) in
  let ⊧ε₁∶φ' : ⊧P ε₁ ∶ φ' 〈 ρ₁ •R ρ 〉
      ⊧ε₁∶φ' = ↠P ⊧P+ε₁∶φ' (Pdirlm P↠refM) in
  let ⊧εε₁∶ψ' : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ' 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ' = ⊧P⊃E (⊧P-change-prop (⊧Prep ⊧ε∶φ'⊃ψ') (≡-sym (rep-•R (φ' ⊃ ψ')))) ⊧ε₁∶φ' in
  let ⊧Q-εε₁∶ψ : ⊧P appP (minus Q 〈 ρ₁ •R ρ 〉) (appP (ε 〈 ρ₁ 〉) ε₁) ∶ ψ 〈 ρ₁ •R ρ 〉
      ⊧Q-εε₁∶ψ = ⊧P⊃E (⊧Prep ⊧Q-∶ψ'⊃ψ) ⊧εε₁∶ψ' in
  let ⊧εε₁∶ψ : ⊧P appP (ε 〈 ρ₁ 〉) ε₁ ∶ ψ 〈 ρ₁ •R ρ 〉
      ⊧εε₁∶ψ = ↠P ⊧Q-εε₁∶ψ (Pdirlm Q↠refN) in
   ↞P (⊧P-change-prop ⊧εε₁∶ψ (rep-•R ψ)) (↠-appP (subst (λ x → appP x (ε 〈 ρ₁ 〉) ↠ ε 〈 ρ₁ 〉) (rep-•R (minus (P ⊃* Q))) (Pdirlm (trans (↠-imp* P↠refM Q↠refN) (inc ref⊃*))))))))
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | reffC M ,p P↠refM | univC _ _ δ ε ,p Q↠univδε = 
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧δ∶ψ⊃ψ' : ⊧P δ ∶ ψ ⊃ ψ'
      ⊧δ∶ψ⊃ψ' = ↠P ⊧Q+∶ψ⊃ψ' (trans (↠-dir Q↠univδε) (inc univplus)) in
  let ⊧ε∶ψ'⊃ψ : ⊧P ε ∶ ψ' ⊃ ψ
      ⊧ε∶ψ'⊃ψ = ↠P ⊧Q-∶ψ'⊃ψ (trans (↠-dir Q↠univδε) (inc univminus)) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ α ⊧α∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ β ⊧β∶φ' → 
  let ⊧β∶φ : ⊧P β ∶ φ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧β∶φ = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧P-∶φ'⊃φ)) ⊧β∶φ') (subst (λ x → x ↠ β) (cong (λ x → appP x β) (cong minus (rep-•R P))) (Pdirlm P↠refM)) in
--(Pdirlm P↠refM)) in
  let ⊧αβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) β ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧αβ∶ψ = ⊧P⊃E (⊧Prep ⊧α∶φ⊃ψ) ⊧β∶φ in
  let ⊧δαβ∶ψ' : ⊧P appP (δ 〈 ρ 〉 〈 ρ₁ 〉) (appP (α 〈 ρ₁ 〉) β) ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧δαβ∶ψ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ∶ψ⊃ψ')) ⊧αβ∶ψ in
  ↞P (subst (λ x → ⊧P x ∶ ((ψ' 〈 ρ 〉) 〈 ρ₁ 〉)) 
    (cong₂ appP (let open ≡-Reasoning in 
    begin
      δ 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎) 
    (cong₂ appP (≡-sym (botSub-upRep (α 〈 ρ₁ 〉))) refl)) 
    ⊧δαβ∶ψ') 
  (trans (↠-appP (↠-appP (↠-dir (↠-imp* (↠-resp-rep (↠-resp-rep P↠refM)) (↠-resp-rep (↠-resp-rep Q↠univδε)))))) 
  (trans (inc (appPl (appPl (dirR ref⊃*univ)))) (trans (inc (appPl (appPl univplus))) (trans (inc (appPl βP)) (inc βP)))))))) ,p
  ⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ α ⊧α∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ β ⊧β∶φ → 
  let ⊧β∶φ' : ⊧P β ∶ φ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧β∶φ' = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧P+∶φ⊃φ')) ⊧β∶φ) (subst (λ x → x ↠ β) (cong (λ x → appP x β) (cong plus (rep-•R P))) (Pdirlm P↠refM)) in
--(Pdirlm P↠refM)) in
  let ⊧αβ∶ψ' : ⊧P appP (α 〈 ρ₁ 〉) β ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
      ⊧αβ∶ψ' = ⊧P⊃E (⊧Prep ⊧α∶φ'⊃ψ') ⊧β∶φ' in
  let ⊧εαβ∶ψ : ⊧P appP (ε 〈 ρ 〉 〈 ρ₁ 〉) (appP (α 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
      ⊧εαβ∶ψ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε∶ψ'⊃ψ)) ⊧αβ∶ψ' in
    ↞P (subst (λ x → ⊧P x ∶ ((ψ 〈 ρ 〉) 〈 ρ₁ 〉)) 
    (cong₂ appP (let open ≡-Reasoning in 
    begin
      ε 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎) 
    (cong₂ appP (≡-sym (botSub-upRep (α 〈 ρ₁ 〉))) refl)) 
    ⊧εαβ∶ψ) 
  (trans (↠-appP (↠-appP (↠-dir (↠-imp* (↠-resp-rep (↠-resp-rep P↠refM)) (↠-resp-rep (↠-resp-rep Q↠univδε)))))) 
  (trans (inc (appPl (appPl (dirR ref⊃*univ)))) (trans (inc (appPl (appPl univminus))) (trans (inc (appPl βP)) (inc βP)))))))
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | univC M M' δ ε ,p P↠univ | reffC N ,p Q↠ref =
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧δ∶φ⊃φ' : ⊧P δ ∶ φ ⊃ φ'
      ⊧δ∶φ⊃φ' = ↠P ⊧P+∶φ⊃φ' (trans (↠-dir P↠univ) (inc univplus)) in
  let ⊧ε∶φ'⊃φ : ⊧P ε ∶ φ' ⊃ φ
      ⊧ε∶φ'⊃φ = ↠P ⊧P-∶φ'⊃φ (trans (↠-dir P↠univ) (inc univminus)) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ α ⊧α∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ β ⊧β∶φ' → 
    let ⊧εβ∶φ : ⊧P appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β ∶ φ 〈 ρ 〉 〈 ρ₁ 〉
        ⊧εβ∶φ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε∶φ'⊃φ)) ⊧β∶φ' in
    let ⊧αεβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αεβ∶ψ = ⊧P⊃E (⊧Prep ⊧α∶φ⊃ψ) ⊧εβ∶φ in
    let ⊧αεβ∶ψ' : ⊧P appP (α 〈 ρ₁ 〉) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αεβ∶ψ' = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧Q+∶ψ⊃ψ')) ⊧αεβ∶ψ) (trans (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep Q↠ref)))) (trans (inc (appPl refdir)) (inc βP))) in
  ↞P ⊧αεβ∶ψ' (trans (↠-appP (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep (↠-imp* P↠univ Q↠ref)))))) (trans (inc (appPl (appPl (dirR univ⊃*ref)))) 
    (trans (inc (appPl (appPl univplus))) (trans (inc (appPl βP)) (inc (subst (λ x → appP ((ΛP (M' 〈 ρ 〉 〈 ρ₁ 〉 ⇑) (appP (var x₁) (appP (ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑) (var x₀)))) ⟦ x₀:= α 〈 ρ₁ 〉 ⟧) β ⇒ x) (cong₂ appP (botSub-upRep (α 〈 ρ₁ 〉)) (cong₂ appP (≡-sym (let open ≡-Reasoning in 
    begin
      ε 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      ε 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎)) refl)) βP))))))))) ,p
  ⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ α ⊧α∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ β ⊧β∶φ → 
    let ⊧δβ∶φ' : ⊧P appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β ∶ φ' 〈 ρ 〉 〈 ρ₁ 〉
        ⊧δβ∶φ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ∶φ⊃φ')) ⊧β∶φ in
    let ⊧αδβ∶ψ' : ⊧P appP (α 〈 ρ₁ 〉) (appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ' 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αδβ∶ψ' = ⊧P⊃E (⊧Prep ⊧α∶φ'⊃ψ') ⊧δβ∶φ' in
    let ⊧αδβ∶ψ : ⊧P appP (α 〈 ρ₁ 〉) (appP (δ 〈 ρ 〉 〈 ρ₁ 〉) β) ∶ ψ 〈 ρ 〉 〈 ρ₁ 〉
        ⊧αδβ∶ψ = ↠P (⊧P⊃E (⊧Prep (⊧Prep ⊧Q-∶ψ'⊃ψ)) ⊧αδβ∶ψ') (trans (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep Q↠ref)))) (trans (inc (appPl refdir)) (inc βP))) in
  ↞P ⊧αδβ∶ψ (trans (↠-appP (↠-appP (↠-dir (↠-resp-rep (↠-resp-rep (↠-imp* P↠univ Q↠ref)))))) 
    (trans (inc (appPl (appPl (dirR univ⊃*ref)))) (trans (inc (appPl (appPl univminus))) (trans (inc (appPl βP)) (inc 
      (subst (λ x → appP ((ΛP (M 〈 ρ 〉 〈 ρ₁ 〉 ⇑) (appP (var x₁) (appP (δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑) (var x₀)))) ⟦ x₀:= α 〈 ρ₁ 〉 ⟧) β ⇒ x) (cong₂ appP (botSub-upRep (α 〈 ρ₁ 〉)) (cong₂ appP (≡-sym (let open ≡-Reasoning in 
    begin
      δ 〈 ρ 〉 〈 ρ₁ 〉
    ≡⟨⟨ botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (rep-congl (botSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉))) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⟦ x₀:= α 〈 ρ₁ 〉 ⟧ ⇑ ⟦ x₀:= β ⟧
    ≡⟨⟨ sub-congl (liftSub-upRep (δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑)) ⟩⟩
      δ 〈 ρ 〉 〈 ρ₁ 〉 ⇑ ⇑ ⟦ liftSub _ (x₀:= α 〈 ρ₁ 〉) ⟧ ⟦ x₀:= β ⟧
    ∎)) refl)) βP))))))))
⊧⊃* {V} {P} {φ} {φ'} {Q} {ψ} {ψ'} (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) | univC M M' δ ε ,p P↠univ | univC N N' δ' ε' ,p Q↠univ =
  let ⊧φ : ⊧T φ ∶ Ω
      ⊧φ = ⊧E-valid₁ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧φ' : ⊧T φ' ∶ Ω
      ⊧φ' = ⊧E-valid₂ (⊧P+∶φ⊃φ' ,p ⊧P-∶φ'⊃φ) in
  let ⊧ψ : ⊧T ψ ∶ Ω
      ⊧ψ = ⊧E-valid₁ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧ψ' : ⊧T ψ' ∶ Ω
      ⊧ψ' = ⊧E-valid₂ (⊧Q+∶ψ⊃ψ' ,p ⊧Q-∶ψ'⊃ψ) in
  let ⊧δ∶φ⊃φ' : ⊧P δ ∶ φ ⊃ φ'
      ⊧δ∶φ⊃φ' = ↠P ⊧P+∶φ⊃φ' (trans (↠-dir P↠univ) (inc univplus)) in
  let ⊧ε∶φ'⊃φ : ⊧P ε ∶ φ' ⊃ φ
      ⊧ε∶φ'⊃φ = ↠P ⊧P-∶φ'⊃φ (trans (↠-dir P↠univ) (inc univminus)) in
  let ⊧δ'∶ψ⊃ψ' : ⊧P δ' ∶ ψ ⊃ ψ'
      ⊧δ'∶ψ⊃ψ' = ↠P ⊧Q+∶ψ⊃ψ' (trans (↠-dir Q↠univ) (inc univplus)) in
  let ⊧ε'∶ψ'⊃ψ : ⊧P ε' ∶ ψ' ⊃ ψ
      ⊧ε'∶ψ'⊃ψ = ↠P ⊧Q-∶ψ'⊃ψ (trans (↠-dir Q↠univ) (inc univminus)) in
  (⊧P⊃I (⊧imp ⊧φ ⊧ψ) (⊧imp ⊧φ' ⊧ψ') (λ W ρ α ⊧α∶φ⊃ψ → 
  ⊧P⊃I (⊧TΩrep ⊧φ') (⊧TΩrep ⊧ψ') (λ W₁ ρ₁ β ⊧β∶φ' → 
  let M* = M 〈 ρ 〉 〈 ρ₁ 〉 in
  let M'* = M' 〈 ρ 〉 〈 ρ₁ 〉 in
  let δ* = δ 〈 ρ 〉 〈 ρ₁ 〉 in
  let ε* = ε 〈 ρ 〉 〈 ρ₁ 〉 in
  let N* = N 〈 ρ 〉 〈 ρ₁ 〉 in
  let N'* = N' 〈 ρ 〉 〈 ρ₁ 〉 in
  let δ'* = δ' 〈 ρ 〉 〈 ρ₁ 〉 in
  let ε'* = ε' 〈 ρ 〉 〈 ρ₁ 〉 in
  let φ* = φ 〈 ρ 〉 〈 ρ₁ 〉 in
  let φ'* = φ' 〈 ρ 〉 〈 ρ₁ 〉 in
  let ψ* = ψ 〈 ρ 〉 〈 ρ₁ 〉 in
  let ψ'* = ψ' 〈 ρ 〉 〈 ρ₁ 〉 in
  let P* = P 〈 ρ 〉 〈 ρ₁ 〉 in
  let Q* = Q 〈 ρ 〉 〈 ρ₁ 〉 in
  let α* = α 〈 ρ₁ 〉 in
  let ⊧εβ∶φ : ⊧P appP ε* β ∶ φ*
      ⊧εβ∶φ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε∶φ'⊃φ)) ⊧β∶φ' in
  let ⊧αεβ∶ψ : ⊧P appP α* (appP ε* β) ∶ ψ*
      ⊧αεβ∶ψ = ⊧P⊃E (⊧Prep ⊧α∶φ⊃ψ) ⊧εβ∶φ in
  let ⊧δ'αεβ∶ψ' : ⊧P appP δ'* (appP α* (appP ε* β)) ∶ ψ'*
      ⊧δ'αεβ∶ψ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ'∶ψ⊃ψ')) ⊧αεβ∶ψ in 
  ↞P ⊧δ'αεβ∶ψ' (let open PreorderReasoning (RTCLOSE _⇒_) in 
    begin
      appP (appP (plus (P* ⊃* Q*)) α*) β
    ∼⟨ ↠-appP (↠-appP (↠-dir (↠-imp* (↠-resp-rep (↠-resp-rep P↠univ)) (↠-resp-rep (↠-resp-rep Q↠univ))))) ⟩
      appP (appP (plus (univ M* M'* δ* ε* ⊃* univ N* N'* δ'* ε'*)) α*) β
    ∼⟨ inc (appPl (appPl (dirR univ⊃*univ))) ⟩
      appP (appP (plus (univ (M* ⊃ N*) (M'* ⊃ N'*) (ΛP (M* ⊃ N*) (ΛP (M'* ⇑) (appP (δ'* ⇑ ⇑) (appP (var x₁) (appP (ε* ⇑ ⇑) (var x₀)))))) (ΛP (M'* ⊃ N'*) (ΛP (M* ⇑) (appP (ε'* ⇑ ⇑) (appP (var x₁) (appP (δ* ⇑ ⇑) (var x₀)))))))) α*) β
    ∼⟨ inc (appPl (appPl univplus)) ⟩
      appP (appP (ΛP (M* ⊃ N*) (ΛP (M'* ⇑) (appP (δ'* ⇑ ⇑) (appP (var x₁) (appP (ε* ⇑ ⇑) (var x₀)))))) α*) β
    ∼⟨ inc (appPl βP) ⟩
      appP (ΛP (M'* ⇑ ⟦ x₀:= α* ⟧) (appP (δ'* ⇑ ⇑ ⟦ liftSub _ (x₀:= α*) ⟧) (appP (α* ⇑) (appP (ε* ⇑ ⇑ ⟦ liftSub _ (x₀:= α*) ⟧) (var x₀))))) β
    ≈⟨ cong₂ appP (cong₂ ΛP (botSub-upRep M'*) (cong₂ appP (liftSub-upRep (δ'* ⇑)) (cong₂ appP refl (cong₂ appP (liftSub-upRep (ε* ⇑)) refl)))) refl ⟩
      appP (ΛP M'* (appP (δ'* ⇑ ⟦ x₀:= α* ⟧ ⇑) (appP (α* ⇑) (appP (ε* ⇑ ⟦ x₀:= α* ⟧ ⇑) (var x₀))))) β
    ≈⟨ cong₂ appP (cong (ΛP M'*) (cong₂ appP (rep-congl (botSub-upRep δ'*)) (cong₂ appP refl (cong₂ appP (rep-congl (botSub-upRep ε*)) refl)))) refl ⟩
      appP (ΛP M'* (appP (δ'* ⇑) (appP (α* ⇑) (appP (ε* ⇑) (var x₀))))) β
    ∼⟨ inc βP ⟩
      appP (δ'* ⇑ ⟦ x₀:= β ⟧) (appP (α* ⇑ ⟦ x₀:= β ⟧) (appP (ε* ⇑ ⟦ x₀:= β ⟧) β))
    ≈⟨ cong₂ appP (botSub-upRep δ'*) (cong₂ appP (botSub-upRep α*) (cong₂ appP (botSub-upRep ε*) refl)) ⟩
      appP δ'* (appP α* (appP ε* β))
    ∎)))),p   
  ⊧P⊃I (⊧imp ⊧φ' ⊧ψ') (⊧imp ⊧φ ⊧ψ) (λ W ρ α ⊧α∶φ'⊃ψ' → 
  ⊧P⊃I (⊧TΩrep ⊧φ) (⊧TΩrep ⊧ψ) (λ W₁ ρ₁ β ⊧β∶φ →
  let M* = M 〈 ρ 〉 〈 ρ₁ 〉 in
  let M'* = M' 〈 ρ 〉 〈 ρ₁ 〉 in
  let δ* = δ 〈 ρ 〉 〈 ρ₁ 〉 in
  let ε* = ε 〈 ρ 〉 〈 ρ₁ 〉 in
  let N* = N 〈 ρ 〉 〈 ρ₁ 〉 in
  let N'* = N' 〈 ρ 〉 〈 ρ₁ 〉 in
  let δ'* = δ' 〈 ρ 〉 〈 ρ₁ 〉 in
  let ε'* = ε' 〈 ρ 〉 〈 ρ₁ 〉 in
  let φ* = φ 〈 ρ 〉 〈 ρ₁ 〉 in
  let φ'* = φ' 〈 ρ 〉 〈 ρ₁ 〉 in
  let ψ* = ψ 〈 ρ 〉 〈 ρ₁ 〉 in
  let ψ'* = ψ' 〈 ρ 〉 〈 ρ₁ 〉 in
  let P* = P 〈 ρ 〉 〈 ρ₁ 〉 in
  let Q* = Q 〈 ρ 〉 〈 ρ₁ 〉 in
  let α* = α 〈 ρ₁ 〉 in
  let ⊧δβ∶φ' : ⊧P appP δ* β ∶ φ'*
      ⊧δβ∶φ' = ⊧P⊃E (⊧Prep (⊧Prep ⊧δ∶φ⊃φ')) ⊧β∶φ in
  let ⊧αδβ∶ψ' : ⊧P appP α* (appP δ* β) ∶ ψ'*
      ⊧αδβ∶ψ' = ⊧P⊃E (⊧Prep ⊧α∶φ'⊃ψ') ⊧δβ∶φ' in
  let ⊧ε'αδβ∶ψ : ⊧P appP ε'* (appP α* (appP δ* β)) ∶ ψ*
      ⊧ε'αδβ∶ψ = ⊧P⊃E (⊧Prep (⊧Prep ⊧ε'∶ψ'⊃ψ)) ⊧αδβ∶ψ' in 
  ↞P ⊧ε'αδβ∶ψ (let open PreorderReasoning (RTCLOSE _⇒_) in 
  begin
    appP (appP (minus (P* ⊃* Q*)) α*) β
  ∼⟨ ↠-appP (↠-appP (↠-dir (↠-imp* (↠-resp-rep (↠-resp-rep P↠univ)) (↠-resp-rep (↠-resp-rep Q↠univ))))) ⟩
    appP (appP (minus (univ M* M'* δ* ε* ⊃* univ N* N'* δ'* ε'*)) α*) β
  ∼⟨ inc (appPl (appPl (dirR univ⊃*univ))) ⟩
    appP (appP (minus (univ (M* ⊃ N*) (M'* ⊃ N'*) (ΛP (M* ⊃ N*) (ΛP (M'* ⇑) (appP (δ'* ⇑ ⇑) (appP (var x₁) (appP (ε* ⇑ ⇑) (var x₀)))))) (ΛP (M'* ⊃ N'*) (ΛP (M* ⇑) (appP (ε'* ⇑ ⇑) (appP (var x₁) (appP (δ* ⇑ ⇑) (var x₀)))))))) α*) β
  ∼⟨ inc (appPl (appPl univminus)) ⟩
    appP (appP (ΛP (M'* ⊃ N'*) (ΛP (M* ⇑) (appP (ε'* ⇑ ⇑) (appP (var x₁) (appP (δ* ⇑ ⇑) (var x₀)))))) α*) β
  ∼⟨ inc (appPl βP) ⟩
    appP (ΛP (M* ⇑ ⟦ x₀:= α* ⟧) (appP (ε'* ⇑ ⇑ ⟦ liftSub _ (x₀:= α*) ⟧) (appP (α* ⇑) (appP (δ* ⇑ ⇑ ⟦ liftSub _ (x₀:= α*) ⟧) (var x₀))))) β
  ≈⟨ cong₂ appP (cong₂ ΛP (botSub-upRep M*) (cong₂ appP (liftSub-upRep (ε'* ⇑)) (cong₂ appP refl (cong₂ appP (liftSub-upRep (δ* ⇑)) refl)))) refl ⟩
    appP (ΛP M* (appP (ε'* ⇑ ⟦ x₀:= α* ⟧ ⇑) (appP (α* ⇑) (appP (δ* ⇑ ⟦ x₀:= α* ⟧ ⇑) (var x₀))))) β
  ≈⟨ cong₂ appP (cong (ΛP M*) (cong₂ appP (rep-congl (botSub-upRep ε'*)) (cong₂ appP refl (cong₂ appP (rep-congl (botSub-upRep δ*)) refl)))) refl ⟩
    appP (ΛP M* (appP (ε'* ⇑) (appP (α* ⇑) (appP (δ* ⇑) (var x₀))))) β
  ∼⟨ inc βP ⟩
    appP (ε'* ⇑ ⟦ x₀:= β ⟧) (appP (α* ⇑ ⟦ x₀:= β ⟧) (appP (δ* ⇑ ⟦ x₀:= β ⟧) β))
  ≈⟨ cong₂ appP (botSub-upRep ε'*) (cong₂ appP (botSub-upRep α*) (cong₂ appP (botSub-upRep δ*) refl)) ⟩
    appP ε'* (appP α* (appP δ* β))
  ∎)))
--TODO Lots of duplication!
