module PHOML.Compute.TermPath where
open import Data.Empty hiding (⊥)
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Canon
open import PHOML.Neutral
open import PHOML.Compute.PC
open import PHOML.Compute.Prp

⊧T_∶_ : ∀ {V} → Term V → Type → Set
⊧E_∶_≡〈_〉_ : ∀ {V} → Path V → Term V → Type → Term V → Set

⊧T M ∶ A = ⊧E M ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧ ∶ M ≡〈 A 〉 M
⊧E P ∶ φ ≡〈 Ω 〉 ψ = ⊧P plus P ∶ φ ⊃ ψ × ⊧P minus P ∶ ψ ⊃ φ
⊧E_∶_≡〈_〉_ {U} P M (A ⇛ B) M' = ∀ V (ρ : Rep U V) N N' Q → ⊧T N ∶ A → ⊧T N' ∶ A → ⊧E Q ∶ N ≡〈 A 〉 N' →
  ⊧E app* N N' (P 〈 ρ 〉) Q ∶ appT (M 〈 ρ 〉) N ≡〈 B 〉 appT (M' 〈 ρ 〉) N'

⊧Erep : ∀ {U V} {P : Path U} {M A N} {ρ : Rep U V} → ⊧E P ∶ M ≡〈 A 〉 N → ⊧E P 〈 ρ 〉 ∶ M 〈 ρ 〉 ≡〈 A 〉 N 〈 ρ 〉
⊧Erep {A = Ω} (⊧P+∶M⊃N ,p ⊧P-∶N⊃M) = ⊧Prep ⊧P+∶M⊃N ,p ⊧Prep ⊧P-∶N⊃M
⊧Erep {P = P} {M} {A = A ⇛ B} {M'} {ρ = ρ} ⊧P∶M≡M' W ρ₁ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = 
  subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) (cong (λ x → app* N N' x Q) (rep-•R P)) (cong (λ x → appT x N) (rep-•R M)) (cong (λ x → appT x N') (rep-•R M')) (⊧P∶M≡M' W (ρ₁ •R ρ) N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N')

⊧Trep : ∀ {U V} (M : Term U) {A} {ρ : Rep U V} → ⊧T M ∶ A → ⊧T M 〈 ρ 〉 ∶ A
⊧Trep {U} {V} M {A} {ρ} ⊧M∶A = subst (λ x → ⊧E x ∶ M 〈 ρ 〉 ≡〈 A 〉 (M 〈 ρ 〉)) 
  (let open ≡-Reasoning in 
    begin
      M ⟦⟦ refSub ∶ idSub U ≡ idSub U ⟧⟧ 〈 ρ 〉
    ≡⟨⟨ pathSub-•RP M ⟩⟩
      M ⟦⟦ refSub •PR ρ ∶ idSub V •SR ρ ≡ idSub V •SR ρ ⟧⟧
    ≡⟨⟨ pathSub-•PR M ⟩⟩
      M 〈 ρ 〉 ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧
    ∎) 
  (⊧Erep ⊧M∶A)
--TODO Flip inputs to pathsub-•PR

⊧E⇛E : ∀ {V} {P : Path V} {M A B M' Q N N'} → ⊧E P ∶ M ≡〈 A ⇛ B 〉 M' → ⊧T N ∶ A → ⊧T N' ∶ A → ⊧E Q ∶ N ≡〈 A 〉 N' → ⊧E app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
⊧E⇛E {V} {P} {M} {A} {B} {M'} {Q} {N} {N'} ⊧P∶M≡M' ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = subst₃ (λ x y z → ⊧E app* N N' x Q ∶ appT y N ≡〈 B 〉 appT z N') rep-idRep rep-idRep
                                                               rep-idRep (⊧P∶M≡M' V (idRep V) N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N')
--A canonical object of type A
c : ∀ {V} → Type → Term V
c Ω = ⊥
c (A ⇛ B) = ΛT A (c B)

conversionE : ∀ {V} {P : Path V} {M M' N N' A} → ⊧E P ∶ M ≡〈 A 〉 N → M ≃ M' → N ≃ N' →
                      ⊧E P ∶ M' ≡〈 A 〉 N'
conversionE {A = Ω} (⊧P+∶φ⊃ψ ,p ⊧P-∶ψ⊃φ) φ≃φ' ψ≃ψ' =
  conversionP ⊧P+∶φ⊃ψ (≃-imp φ≃φ' ψ≃ψ') ,p conversionP ⊧P-∶ψ⊃φ (≃-imp ψ≃ψ' φ≃φ')
conversionE {A = A ⇛ B} ⊧P∶M≡N M≃M' N≃N' W ρ L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = 
  conversionE {A = B} (⊧P∶M≡N W ρ L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L') (≃-appTl (≃-resp-rep M≃M')) (≃-appTl (≃-resp-rep N≃N'))

expansionT : ∀ {V} {M N : Term V} {A} → ⊧T N ∶ A → M ⇒ N → ⊧T M ∶ A
expansionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E Q ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E P ∶ M ≡〈 A 〉 N

expansionT ⊧N∶A M⇒N = conversionE (expansionE ⊧N∶A (⇒-resp-ps M⇒N)) (sym (inc M⇒N)) (sym (inc M⇒N))

expansionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  expansionP ⊧Q+∶φ⊃ψ (dirR P⇒Q) ,p expansionP ⊧Q-∶ψ⊃φ (dirR P⇒Q)
expansionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q W ρ N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = expansionE (⊧Q∶M≡M' W ρ N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l (⇒-resp-rep P⇒Q))

c-closedE : ∀ {U U' V W} A {ρ₁ ρ₂ ρ₁' ρ₂'} {τ' : PathSub U' W} {τ : PathSub U V} {σ : Sub V W} →
                    c A ⟦⟦ τ ∶ ρ₁ ≡ ρ₂ ⟧⟧ ⟦ σ ⟧ ≡ c A ⟦⟦ τ' ∶ ρ₁' ≡ ρ₂' ⟧⟧
c-closedE Ω = refl
c-closedE (A ⇛ B) = cong (λλλ A) (c-closedE B)

c-closedR : ∀ {U V} A {ρ : Rep U V} → c A 〈 ρ 〉 ≡ c A
c-closedR Ω = refl
c-closedR (A ⇛ B) = cong (ΛT A) (c-closedR B)

c-closed : ∀ {U V} A {σ : Sub U V} → c A ⟦ σ ⟧ ≡ c A
c-closed Ω = refl
c-closed (A ⇛ B) = cong (ΛT A) (c-closed B)

⊧c : ∀ {V A} → ⊧T c {V} A ∶ A
⊧c {A = Ω} = (imp bot bot ,p ref ,p (λ {W ρ ε (ε' ,p ε↠ε') → ε' ,p trans (inc (appPl refdir)) (trans (inc βP) ε↠ε')})) ,p imp bot bot ,p ref ,p 
  λ {W ρ ε (ε' ,p ε↠ε') → ε' ,p trans (inc (appPl refdir)) (trans (inc βP) ε↠ε')}
⊧c {V} {A = A ⇛ B} W ρ N N' Q ⊧N∶A ⊧N'∶A ⊧Q∶N≡N' = expansionE 
  (conversionE 
    (subst₃ (λ x y z → ⊧E x ∶ y ≡〈 B 〉 z) 
      (let open ≡-Reasoning in 
      begin
        c B ⟦⟦ refSub ∶ idSub W ≡ idSub W ⟧⟧
      ≡⟨⟨ c-closedE B ⟩⟩
        c B ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ ⟦ (x₂:= N ,x₁:= N' ,x₀:= Q) •SR liftsRep pathDom ρ ⟧
      ≡⟨ sub-•SR (c B ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧) ⟩
        c B ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= N ,x₁:= N' ,x₀:= Q ⟧
      ∎) (≡-sym (≡-trans (sub-congl (c-closedR B)) (c-closed B))) (≡-sym (≡-trans (sub-congl (c-closedR B)) (c-closed B))) (⊧c {A = B}))
    (sym (inc βT)) (sym (inc βT))) 
  βE

⊧E-wn : ∀ {V} {P : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → Σ[ Q ∈ CanonE V ] P ↠ decode-CanonE Q
⊧E-wn {A = Ω} (⊧P+∶M⊃N ,p _) with Lemma35e ⊧P+∶M⊃N
⊧E-wn {P = P} {A = Ω} (⊧P+∶M⊃N ,p _) | (P' ,p P↠P') = CanonΩ2CanonE P' ,p subst (λ x → P ↠ x) (decode-CanonΩE {P = P'}) P↠P'
⊧E-wn {V} {A = A ⇛ B} ⊧P∶M≡N = let 
  P'cA ,p PcA↠P'cA = ⊧E-wn (⊧P∶M≡N V (idRep V) (c A) (c A) (c A ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧) ⊧c ⊧c ⊧c) in 
  app*-wnl {R = P'cA} PcA↠P'cA (cong₄ app* refl refl rep-idRep refl)

↞E : ∀ {V} {P Q : Path V} {M A N} → ⊧E Q ∶ M ≡〈 A 〉 N → P ↠ Q → ⊧E P ∶ M ≡〈 A 〉 N
↞E ⊧Q∶M≡N (inc P⇒Q) = expansionE ⊧Q∶M≡N P⇒Q
↞E ⊧Q∶M≡N ref = ⊧Q∶M≡N
↞E ⊧Q∶M≡N (trans P↠P' P'↠Q) = ↞E (↞E ⊧Q∶M≡N P'↠Q) P↠P'
--TODO Duplication

reductionT : ∀ {V} {M N : Term V} {A} → ⊧T M ∶ A → M ⇒ N → ⊧T N ∶ A
reductionE : ∀ {V} {P Q : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → P ⇒ Q → ⊧E Q ∶ M ≡〈 A 〉 N

reductionT ⊧N∶A M⇒N = conversionE (reductionE ⊧N∶A (⇒-resp-ps M⇒N)) (inc M⇒N) (inc M⇒N)

reductionE {A = Ω} (⊧Q+∶φ⊃ψ ,p ⊧Q-∶ψ⊃φ) P⇒Q = 
  reductionP ⊧Q+∶φ⊃ψ (dirR P⇒Q) ,p reductionP ⊧Q-∶ψ⊃φ (dirR P⇒Q)
reductionE {A = A ⇛ B} ⊧Q∶M≡M' P⇒Q W ρ N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N' = reductionE (⊧Q∶M≡M' W ρ N N' R ⊧N∶A ⊧N'∶A ⊧R∶N≡N') (app*l (⇒-resp-rep P⇒Q))
--TODO Duplication

↠T : ∀ {V} {M N : Term V} {A} → ⊧T M ∶ A → M ↠ N → ⊧T N ∶ A
↠T ⊧M∶A (inc M⇒N) = reductionT ⊧M∶A M⇒N
↠T ⊧M∶A ref = ⊧M∶A
↠T ⊧M∶A (trans M↠N N↠N') = ↠T (↠T ⊧M∶A M↠N) N↠N'

↠E : ∀ {V} {P Q : Path V} {M A N} → ⊧E P ∶ M ≡〈 A 〉 N → P ↠ Q → ⊧E Q ∶ M ≡〈 A 〉 N
↠E ⊧P∶M≡N (inc P⇒Q) = reductionE ⊧P∶M≡N P⇒Q
↠E ⊧P∶M≡N ref = ⊧P∶M≡N
↠E ⊧P∶M≡N (trans P↠Q Q↠R) = ↠E (↠E ⊧P∶M≡N P↠Q) Q↠R

APPl-rtΛ : ∀ {V P M N} {NN : snocList (Term V)} {A L} →
                   ⊧E P ∶ APPl (appT M N) NN ≡〈 A 〉 L → Reduces-to-Λ M
APPl-rtΛ {A = Ω} ((bot ,p MNN⊃N↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot MNN⊃N↠⊥)
APPl-rtΛ {M = M} {N} {NN = NN} {A = Ω} ((imp θ θ' ,p MNN⊃N↠θ⊃θ' ,p proj₂) ,p proj₃ ,p proj₄ ,p proj₅) = 
  APPl-red-canon {NN = NN} {θ = θ} (imp-red-inj₁ MNN⊃N↠θ⊃θ')
APPl-rtΛ {V} {P} {M} {N} {NN} {A ⇛ B} {L} ⊧P∶MNN≡N = APPl-rtΛ {V}
  {app* (c A) (c A) P (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)} {M} {N}
  {NN snoc c A} {B} {appT L (c A)} 
  (⊧E⇛E ⊧P∶MNN≡N ⊧c ⊧c ⊧c)

⊧E-rtΛ : ∀ {V} {P : Path V} {M N A B} → ⊧E P ∶ M ≡〈 A ⇛ B 〉 N → Reduces-to-Λ M
⊧E-rtΛ {V} {P} {M} {N} {A} {B} ⊧P∶M≡N = APPl-rtΛ {V}
                                             {app* (c A) (c A) P (c A ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)} {M}
                                             {c A} {[]} {B} {appT N (c A)} 
          (⊧E⇛E ⊧P∶M≡N ⊧c ⊧c ⊧c)
--TODO Duplication

⊧T-rtΛ : ∀ {V} {M : Term V} {A B} → ⊧T M ∶ A ⇛ B → Reduces-to-Λ M
⊧T-rtΛ {V} {M} ⊧M∶A⇛B = ⊧E-rtΛ {P = M ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧} {N = M} ⊧M∶A⇛B

⊧refP : ∀ {V} {M φ : Term V} {θ} → φ ↠ decode θ → ⊧E reff M ∶ φ ≡〈 Ω 〉 φ
⊧refP {V} {M} {φ} {θ} φ↠θ = 
  (imp θ θ ,p ↠-imp φ↠θ φ↠θ ,p (λ W ρ ε ⊧ε∶θ → ↞PC ⊧ε∶θ (trans (inc (appPl refdir)) (inc βP)))) ,p 
  imp θ θ ,p ↠-imp φ↠θ φ↠θ ,p (λ ε W ρ ⊧ε∶φ → ↞PC ⊧ε∶φ (trans (inc (appPl refdir)) (inc βP)))

⊧canon : ∀ {V} {φ : Term V} → ⊧T φ ∶ Ω → Σ[ θ ∈ CanonProp ] φ ↠ decode θ
⊧canon ((bot ,p φ⊃φ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃φ↠⊥)
⊧canon ((imp θ θ' ,p φ⊃φ↠θ⊃θ' ,p _) ,p _) = θ ,p (imp-red-inj₁ φ⊃φ↠θ⊃θ')

⊧canon' : ∀ {V} {φ : Term V} (θ : CanonProp) → φ ↠ decode θ → ⊧T φ ∶ Ω
⊧canon' {V} {φ} θ φ↠θ = (imp θ θ ,p (↠-imp φ↠θ φ↠θ) ,p (λ W ρ ε ⊧ε∶φ → ↞PC (↞PC ⊧ε∶φ (trans (inc (appPl refdir)) (inc βP))) (↠-appP (↠-dir (↠-resp-rep (trans (↠-resp-ps φ↠θ) (θps-red-ref θ))))))) ,p 
  imp θ θ ,p (↠-imp φ↠θ φ↠θ) ,p (λ W ρ ε ⊧ε∶φ → ↞PC (↞PC ⊧ε∶φ (trans (inc (appPl refdir)) (inc βP))) (↠-appP (↠-dir (↠-resp-rep (trans (↠-resp-ps φ↠θ) (θps-red-ref θ))))))

⊧TΩrep : ∀ {U V} {φ : Term U} {ρ : Rep U V} → ⊧T φ ∶ Ω → ⊧T φ 〈 ρ 〉 ∶ Ω
⊧TΩrep ⊧φ = let θ ,p φ↠θ = ⊧canon ⊧φ in ⊧canon' θ (rep-red-canon θ φ↠θ)

⊧P⊃I : ∀ {V} {φ ψ : Term V} {δ} →
  ⊧T φ ∶ Ω → ⊧T ψ ∶ Ω →
  (∀ W (ρ : Rep V W) ε → ⊧P ε ∶ φ 〈 ρ 〉 → ⊧P appP (δ 〈 ρ 〉) ε ∶ ψ 〈 ρ 〉) →
  ⊧P δ ∶ φ ⊃ ψ
⊧P⊃I {φ = φ} {ψ} ⊧φ∶Ω ⊧ψ∶Ω hyp =
  let θ ,p φ↠θ = ⊧canon ⊧φ∶Ω in 
  let θ' ,p ψ↠θ' = ⊧canon ⊧ψ∶Ω in 
  imp θ θ' ,p ↠-imp φ↠θ ψ↠θ' ,p λ W ρ ε ⊧ε∶φ → 
    ⊧P-out (hyp W ρ ε (θ ,p rep-red-canon θ φ↠θ ,p ⊧ε∶φ)) (rep-red-canon θ' ψ↠θ')

⊧neutralP' : ∀ {V} {δ : NeutralP V} {φ : Term V} → ⊧T φ ∶ Ω → ⊧P decode-NeutralP δ ∶ φ
⊧neutralP' {δ = δ} ⊧φ∶Ω = let θ ,p φ↠θ = ⊧canon ⊧φ∶Ω in ⊧neutralP {δ = δ} {θ = θ} φ↠θ

⊧appT : ∀ {V A B} {M N : Term V} → ⊧T M ∶ A ⇛ B → ⊧T N ∶ A → ⊧T appT M N ∶ B
⊧appT {A = A} {B} {M} {N} ⊧M∶A⇛B ⊧N∶A = subst (λ x → ⊧E x ∶ appT M N ≡〈 B 〉 appT M N) 
  (cong₂ (λ x y → app* x y (M ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧) (N ⟦⟦ refSub ∶ idSub _ ≡ idSub _ ⟧⟧)) (≡-sym sub-idSub) (≡-sym sub-idSub))
  (⊧E⇛E ⊧M∶A⇛B ⊧N∶A ⊧N∶A ⊧N∶A)

⊧neutralE : ∀ {V} {P : NeutralE V} {M A N} → ⊧T M ∶ A → ⊧T N ∶ A → ⊧E decode-NeutralE P ∶ M ≡〈 A 〉 N
⊧neutralE {P = P} {A = Ω} ⊧M∶Ω ⊧N∶Ω =
  let θ ,p M↠θ = ⊧canon ⊧M∶Ω in 
  let θ' ,p N↠θ' = ⊧canon ⊧N∶Ω in (imp θ θ' ,p (↠-imp M↠θ N↠θ') ,p (λ W ρ ε ⊧ε∶φ → subst (λ x → ⊧PC x ∶ θ') (cong (λ x → appP (plus x) ε) (decode-nrepE P)) (⊧neutralPC (app (dirN -plus (nrepE ρ P)) ε)))) ,p (imp θ' θ) ,p (↠-imp N↠θ' M↠θ ,p (λ W ρ ε ⊧ε∶φ → subst (λ x → ⊧PC x ∶ θ) (cong (λ x → appP (minus x) ε) (decode-nrepE P)) (⊧neutralPC (app (dirN -minus (nrepE ρ P)) ε))))
⊧neutralE {P = P} {M} {A = A ⇛ B} {N} ⊧M∶A⇛B ⊧N∶A⇛B W ρ L L' Q ⊧L∶A ⊧L'∶A ⊧Q∶L≡L' = subst (λ x → ⊧E x ∶ appT (M 〈 ρ 〉) L ≡〈 B 〉 appT (N 〈 ρ 〉) L') (cong (λ x → app* L L' x Q) (decode-nrepE P)) 
  (⊧neutralE {P = app*N L L' (nrepE ρ P) Q} (⊧appT (⊧Trep M ⊧M∶A⇛B) ⊧L∶A) (⊧appT (⊧Trep N ⊧N∶A⇛B) ⊧L'∶A))

private ⊧reflm : ∀ {U V} {M N : Term V} {P} {ρ : Rep U V} → ((x₂:= M ,x₁:= N ,x₀:= P) •SR liftsRep pathDom ρ •SP liftPathSub refSub) ∼∼ ((x₀::= P) •PR liftRep -Term ρ)
⊧reflm x₀ = refl
⊧reflm (↑ x) = refl

private ⊧reflm₂ : ∀ {U V} {M N : Term V} {P} {ρ : Rep U V} → ((x₂:= M ,x₁:= N ,x₀:= P) •SR liftsRep pathDom ρ • sub↖ (idSub U)) ∼ ((x₀:= M) •SR liftRep -Term ρ)
⊧reflm₂ x₀ = refl
⊧reflm₂ (↑ x) = refl

private ⊧reflm₃ : ∀ {U V} {M N : Term V} {P} {ρ : Rep U V} → ((x₂:= M ,x₁:= N ,x₀:= P) •SR liftsRep pathDom ρ • sub↗ (idSub U)) ∼ ((x₀:= N) •SR liftRep -Term ρ)
⊧reflm₃ x₀ = refl
⊧reflm₃ (↑ x) = refl

⊧ref : ∀ {V} {M : Term V} {A} → ⊧T M ∶ A → ⊧E reff M ∶ M ≡〈 A 〉 M
⊧ref {V} {M} {A = Ω} ⊧M∶Ω = let θ ,p M↠θ = ⊧canon ⊧M∶Ω in ⊧refP {θ = θ} M↠θ
⊧ref {V} {M} {A = A ⇛ B} ⊧M∶A⇛B W ρ L L' P ⊧L∶A ⊧L'∶A ⊧P∶L≡L' =
  let reduces-to-Λ C N M↠ΛCN = ⊧T-rtΛ {V} {M} {A} {B} ⊧M∶A⇛B in 
  let ΛCNx≃Mx : ∀ x → N 〈 liftRep _ ρ 〉 ⟦ x₀:= x ⟧ ≃ appT (M 〈 ρ 〉) x
      ΛCNx≃Mx x = sym (trans (≃-appTl (≃-resp-rep (sub-RT-RST M↠ΛCN))) (inc βT)) in
  let ⊧ΛCN∶A⇛B : ⊧T ΛT C N ∶ A ⇛ B
      ⊧ΛCN∶A⇛B = ↠T ⊧M∶A⇛B M↠ΛCN in
  let ⊧λλλNP : ⊧E app* L L' (λλλ C (N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉)) P ∶
             appT (ΛT C (N 〈 liftRep _ ρ 〉)) L ≡〈 B 〉 appT (ΛT C (N 〈 liftRep _ ρ 〉)) L'
      ⊧λλλNP = ⊧ΛCN∶A⇛B W ρ L L' P ⊧L∶A ⊧L'∶A ⊧P∶L≡L' in
  let ⊧N⟦⟦P⟧⟧ : ⊧E N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= P ⟧ ∶ appT (ΛT C (N 〈 liftRep _ ρ 〉)) L ≡〈 B 〉 appT (ΛT C (N 〈 liftRep _ ρ 〉)) L'
      ⊧N⟦⟦P⟧⟧ = reductionE ⊧λλλNP βE in
  let ⊧N⟦⟦P⟧⟧ : ⊧E N 〈 liftRep _ ρ 〉 ⟦⟦ x₀::= P ∶ x₀:= L ≡ x₀:= L' ⟧⟧ ∶ appT (ΛT C (N 〈 liftRep _ ρ 〉)) L ≡〈 B 〉 appT (ΛT C (N 〈 liftRep _ ρ 〉)) L'
      ⊧N⟦⟦P⟧⟧ = subst
                  (λ x →
                     ⊧E x ∶ appT (ΛT C (N 〈 liftRep _ ρ 〉)) L ≡〈 B 〉
                     appT (ΛT C (N 〈 liftRep _ ρ 〉)) L')
                  (let open ≡-Reasoning in 
                    begin
                      N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ 〈 liftsRep pathDom ρ 〉 ⟦ x₂:= L ,x₁:= L' ,x₀:= P ⟧
                    ≡⟨⟨ sub-•SR (N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧) ⟩⟩
                      N ⟦⟦ liftPathSub refSub ∶ sub↖ (idSub V) ≡ sub↗ (idSub V) ⟧⟧ ⟦ (x₂:= L ,x₁:= L' ,x₀:= P) •SR liftsRep pathDom ρ ⟧
                    ≡⟨⟨ pathSub-•SP N ⟩⟩
                      N ⟦⟦ (x₂:= L ,x₁:= L' ,x₀:= P) •SR liftsRep pathDom ρ •SP liftPathSub refSub ∶ (x₂:= L ,x₁:= L' ,x₀:= P) •SR liftsRep pathDom ρ • sub↖ (idSub V) ≡ (x₂:= L ,x₁:= L' ,x₀:= P) •SR liftsRep pathDom ρ • sub↗ (idSub V) ⟧⟧
                    ≡⟨ pathSub-cong N ⊧reflm ⊧reflm₂ ⊧reflm₃ ⟩
                      N ⟦⟦ x₀::= P •PR liftRep _ ρ ∶ x₀:= L •SR liftRep _ ρ ≡ x₀:= L' •SR liftRep _ ρ ⟧⟧
                    ≡⟨⟨ pathSub-•PR N ⟩⟩
                      N 〈 liftRep _ ρ 〉 ⟦⟦ x₀::= P ∶ x₀:= L ≡ x₀:= L' ⟧⟧
                    ∎) ⊧N⟦⟦P⟧⟧ in
  let ⊧N⟦⟦P⟧⟧ : ⊧E N 〈 liftRep _ ρ 〉 ⟦⟦ x₀::= P ∶ x₀:= L ≡ x₀:= L' ⟧⟧ ∶ N 〈 liftRep _ ρ 〉 ⟦ x₀:= L ⟧ ≡〈 B 〉 N 〈 liftRep _ ρ 〉 ⟦ x₀:= L' ⟧
      ⊧N⟦⟦P⟧⟧ = conversionE ⊧N⟦⟦P⟧⟧ (inc βT) (inc βT) in
  let ⊧refMP : ⊧E app* L L' (reff M 〈 ρ 〉) P ∶ N 〈 liftRep _ ρ 〉 ⟦ x₀:= L ⟧ ≡〈 B 〉 N 〈 liftRep _ ρ 〉 ⟦ x₀:= L' ⟧
      ⊧refMP = ↞E ⊧N⟦⟦P⟧⟧ (trans (↠-app*ref (↠-resp-rep M↠ΛCN)) (inc βPP)) in
  conversionE ⊧refMP (ΛCNx≃Mx L) (ΛCNx≃Mx L')

⊧E-valid₁ : ∀ {V} {P : Path V} {φ ψ : Term V} → ⊧E P ∶ φ ≡〈 Ω 〉 ψ → ⊧T φ ∶ Ω
⊧E-valid₁ ((bot ,p φ⊃ψ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧E-valid₁ ((imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p _) ,p _) = ⊧canon' θ (imp-red-inj₁ φ⊃ψ↠θ⊃θ')

⊧E-valid₂ : ∀ {V} {P : Path V} {φ ψ : Term V} → ⊧E P ∶ φ ≡〈 Ω 〉 ψ → ⊧T ψ ∶ Ω
⊧E-valid₂ ((bot ,p φ⊃ψ↠⊥ ,p _) ,p _) = ⊥-elim (imp-not-red-bot φ⊃ψ↠⊥)
⊧E-valid₂ ((imp θ θ' ,p φ⊃ψ↠θ⊃θ' ,p proj₂) ,p proj₄) = ⊧canon' θ' (imp-red-inj₂ φ⊃ψ↠θ⊃θ')

⊧imp : ∀ {V} {φ ψ : Term V} → ⊧T φ ∶ Ω → ⊧T ψ ∶ Ω → ⊧T φ ⊃ ψ ∶ Ω
⊧imp ⊧Tφ ⊧Tψ = let θ ,p φ↠θ = ⊧canon ⊧Tφ in 
  let θ' ,p ψ↠θ' = ⊧canon ⊧Tψ in ⊧canon' (imp θ θ') (↠-imp φ↠θ ψ↠θ')

⊧univ : ∀ {V} {φ ψ : Term V} {δ ε} → ⊧P δ ∶ φ ⊃ ψ → ⊧P ε ∶ ψ ⊃ φ → ⊧E univ φ ψ δ ε ∶ φ ≡〈 Ω 〉 ψ
⊧univ ⊧δ∶φ⊃ψ ⊧ε∶ψ⊃φ = expansionP ⊧δ∶φ⊃ψ univplus ,p expansionP ⊧ε∶ψ⊃φ univminus

