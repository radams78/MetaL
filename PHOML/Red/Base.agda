module PHOML.Red.Base where

open import Level
open import Data.Bool
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub

infix 10 _⇒_
data _⇒_ : ∀ {V K} → Expression V K → Expression V K → Set where
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ⇒ M ⟦ x₀:= N ⟧
  appTl : ∀ {V} {M M' N : Term V} → M ⇒ M' → appT M N ⇒ appT M' N
  impl : ∀ {V} {φ φ' ψ : Term V} → φ ⇒ φ' → φ ⊃ ψ ⇒ φ' ⊃ ψ
  impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ⇒ ψ' → φ ⊃ ψ ⇒ φ ⊃ ψ'
  βP : ∀ {V} {φ : Term V} {δ ε} → appP (ΛP φ δ) ε ⇒ δ ⟦ x₀:= ε ⟧
  refdir : ∀ {V} {φ : Term V} {d} → dir d (reff φ) ⇒ id φ
  univplus : ∀ {V} {φ ψ : Term V} {δ ε} → plus (univ φ ψ δ ε) ⇒ δ
  univminus : ∀ {V} {φ ψ : Term V} {δ ε} → minus (univ φ ψ δ ε) ⇒ ε
  appPl : ∀ {V} {δ δ' ε : Proof V} → δ ⇒ δ' → appP δ ε ⇒ appP δ' ε
  dirR : ∀ {V d} {P Q : Path V} → P ⇒ Q → dir d P ⇒ dir d Q
  βE : ∀ {V A M N P} {Q : Path V} → app* M N (λλλ A P) Q ⇒ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  βPP : ∀ {V A M} {N N' : Term V} {P} → app* N N' (reff (ΛT A M)) P ⇒ M ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧
  ref⊃* : ∀ {V} {φ ψ : Term V} → reff φ ⊃* reff ψ ⇒ reff (φ ⊃ ψ)
  ref⊃*univ : ∀ {V} {φ ψ χ : Term V} {δ ε} → 
    reff φ ⊃* univ ψ χ δ ε ⇒ univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀)))))
  univ⊃*ref : ∀ {V} {φ ψ χ : Term V} {δ ε} →
    univ φ ψ δ ε ⊃* reff χ ⇒ univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀)))))
  univ⊃*univ : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε'} →
    univ φ ψ δ ε ⊃* univ φ' ψ' δ' ε' ⇒ univ (φ ⊃ φ') (ψ ⊃ ψ') (ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀)))))) (ΛP (ψ ⊃ ψ') (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
  app*l : ∀ {V} {M N : Term V} {P P' Q} → P ⇒ P' → app* M N P Q ⇒ app* M N P' Q
  reffR : ∀ {V} {M M' N N' : Term V} {P} → M ⇒ M' → app* N N' (reff M) P ⇒ app* N N' (reff M') P
  imp*l : ∀ {V} {P P' Q : Path V} → P ⇒ P' → P ⊃* Q ⇒ P' ⊃* Q
  imp*r : ∀ {V} {P Q Q' : Path V} → Q ⇒ Q' → P ⊃* Q ⇒ P ⊃* Q'

⇒-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ⇒ F → E 〈 ρ 〉 ⇒ F 〈 ρ 〉
⇒-resp-rep {ρ = ρ} (βT {V} {A} {M} {N}) = subst (λ x → (appT (ΛT A M) N 〈 ρ 〉) ⇒ x) 
  (≡-sym (•RS-botSub M))
  βT
⇒-resp-rep (appTl M⇒M') = appTl (⇒-resp-rep M⇒M')
⇒-resp-rep (impl φ⇒φ') = impl (⇒-resp-rep φ⇒φ')
⇒-resp-rep (impr ψ⇒ψ') = impr (⇒-resp-rep ψ⇒ψ')
⇒-resp-rep {ρ = ρ} (βP {φ = φ} {δ} {ε}) = subst (λ x → (appP (ΛP φ δ) ε) 〈 ρ 〉 ⇒ x) (≡-sym (•RS-botSub δ)) βP
⇒-resp-rep (appPl δ⇒δ') = appPl (⇒-resp-rep δ⇒δ')
⇒-resp-rep (dirR P⇒P') = dirR (⇒-resp-rep P⇒P')
⇒-resp-rep refdir = refdir
⇒-resp-rep univplus = univplus
⇒-resp-rep univminus = univminus
⇒-resp-rep {ρ = ρ} (βE {A = A} {M} {N} {P} {Q}) = subst (λ x → (app* M N (λλλ A P) Q 〈 ρ 〉) ⇒ x) (botSub₃-liftRep₃ P) βE
⇒-resp-rep {ρ = ρ} (βPP {V} {A} {M} {N} {N'} {P}) = subst (λ x → (app* N N' (reff (ΛT A M)) P) 〈 ρ 〉 ⇒ x) 
  (let open ≡-Reasoning in 
  begin
    M 〈 liftRep -Term ρ 〉 ⟦⟦ x₀::= (P 〈 ρ 〉) ∶ x₀:= N 〈 ρ 〉 ≡ x₀:= N' 〈 ρ 〉 ⟧⟧
  ≡⟨ pathSub-•PR M ⟩
    M ⟦⟦ x₀::= (P 〈 ρ 〉) •PR liftRep -Term ρ ∶ x₀:= N 〈 ρ 〉 •SR liftRep -Term ρ ≡
         x₀:= N' 〈 ρ 〉 •SR liftRep -Term ρ ⟧⟧
  ≡⟨⟨ pathSub-cong M botPathSub-liftRep' (comp-botSub' COMPRS COMPSR) (comp-botSub' COMPRS COMPSR) ⟩⟩
    M ⟦⟦ ρ •RP x₀::= P ∶ ρ •RS x₀:= N ≡ ρ •RS x₀:= N' ⟧⟧
  ≡⟨ pathSub-•RP M ⟩
    M ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧ 〈 ρ 〉
  ∎) 
  βPP
⇒-resp-rep ref⊃* = ref⊃*
⇒-resp-rep {ρ = ρ} (ref⊃*univ {φ = φ} {ψ} {ψ'} {δ} {ε}) = subst (λ x → (reff φ ⊃* univ ψ ψ' δ ε) 〈 ρ 〉 ⇒ x) 
  (cong₂ (λ x y → univ ((φ ⊃ ψ) 〈 ρ 〉) ((φ ⊃ ψ') 〈 ρ 〉) (ΛP ((φ ⊃ ψ) 〈 ρ 〉) x) (ΛP ((φ ⊃ ψ') 〈 ρ 〉) y)) 
    (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP (≡-sym (liftRep-upRep₂ δ)) refl)) 
    (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP (≡-sym (liftRep-upRep₂ ε)) refl))) 
  ref⊃*univ
⇒-resp-rep {ρ = ρ} (univ⊃*ref {φ = φ} {φ'} {ψ} {δ = δ} {ε = ε}) = subst (λ x → (univ φ φ' δ ε ⊃* reff ψ) 〈 ρ 〉 ⇒ x) 
  (cong₂ (univ _ _) (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ')) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ ε)) refl)))) 
  (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ δ)) refl))))) 
  univ⊃*ref
⇒-resp-rep {ρ = ρ} (univ⊃*univ {φ = φ} {φ'} {ψ} {ψ'} {δ} {δ'} {ε} {ε'}) = subst (λ x → (univ φ ψ δ ε ⊃* univ φ' ψ' δ' ε') 〈 ρ 〉 ⇒ x) 
  (cong₂ (univ _ _) 
    (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep ψ)) (cong₂ appP (≡-sym (liftRep-upRep₂ δ')) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ ε)) refl))))) 
    (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP (≡-sym (liftRep-upRep₂ ε')) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ δ)) refl)))))) 
  univ⊃*univ
⇒-resp-rep (imp*l P⇒P') = imp*l (⇒-resp-rep P⇒P')
⇒-resp-rep (imp*r Q⇒Q') = imp*r (⇒-resp-rep Q⇒Q')
⇒-resp-rep (app*l P⇒P') = app*l (⇒-resp-rep P⇒P')
⇒-resp-rep (reffR M⇒N) = reffR (⇒-resp-rep M⇒N)

⇒-resp-sub : ∀ {U V} {M N : Term U} {σ : Sub U V} → M ⇒ N → M ⟦ σ ⟧ ⇒ N ⟦ σ ⟧
⇒-resp-sub {σ = σ} (βT {A = A} {M} {N}) = subst (λ x → appT (ΛT A (M ⟦ liftSub _ σ ⟧)) (N ⟦ σ ⟧) ⇒ x) (≡-sym (•-botSub'' M)) βT
⇒-resp-sub (appTl E⇒F) = appTl (⇒-resp-sub E⇒F)
⇒-resp-sub (impl E⇒F) = impl (⇒-resp-sub E⇒F)
⇒-resp-sub (impr E⇒F) = impr (⇒-resp-sub E⇒F)

⇒-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ⇒ N → M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ⇒ N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧
⇒-resp-ps {V = V} {τ = τ} {ρ} {σ} (βT {U} {A} {M} {N}) = 
  let μ : Sub (extend V pathDom) V
      μ = x₂:= N ⟦ ρ ⟧ ,x₁:= N ⟦ σ ⟧ ,x₀:= N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ in
  subst (λ x → app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧) (λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧))
    (N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧) ⇒ x) 
  (let open ≡-Reasoning in 
  begin
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ⟧⟧ ⟦ μ ⟧
  ≡⟨⟨ pathSub-•SP M ⟩⟩
    M ⟦⟦ μ •SP liftPathSub τ ∶ μ • sub↖ ρ ≡ μ • sub↗ σ ⟧⟧
  ≡⟨⟨ pathSub-cong M •SP-botSub sub↖-botSub sub↗-botSub ⟩⟩
    M ⟦⟦ τ ∶ ρ ≡ σ •PS (x₀:= N) ∶ ρ • (x₀:= N) ≡ σ • (x₀:= N) ⟧⟧
  ≡⟨ pathSub-•PS M ⟩
    (M ⟦ x₀:= N ⟧) ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧
  ∎) 
  βE
⇒-resp-ps (appTl M⇒M') = app*l (⇒-resp-ps M⇒M')
⇒-resp-ps (impl φ⇒φ') = imp*l (⇒-resp-ps φ⇒φ')
⇒-resp-ps (impr ψ⇒ψ') = imp*r (⇒-resp-ps ψ⇒ψ')

⇒-APPP : ∀ {V} {δ δ' : Proof V} εε → δ ⇒ δ' → APPP δ εε ⇒ APPP δ' εε
⇒-APPP [] δ⇒δ' = δ⇒δ'
⇒-APPP (εε snoc ε) δ⇒δ' = appPl (⇒-APPP εε δ⇒δ')

-- If MN1...Nn -> N with n >= 1 then either N = M'N1...Nn where M -> M', or M is a lambda-term
APPl-⇒ : ∀ {V M N M' N'} (NN : snocList (Term V)) →
  M ⇒ N → M ≡ APPl (appT M' N') NN → Σ[ M'' ∈ Term V ] (M' ⇒ M'' × N ≡ APPl (appT M'' N') NN) ⊎ Σ[ A ∈ Type ] Σ[ M'' ∈ Term (V , -Term) ] M' ≡ ΛT A M''
APPl-⇒ NN βT M≡M'NN = inj₂ (_ ,p _ ,p (APPl-Λ {NN = NN} (≡-sym M≡M'NN)))
APPl-⇒ [] (appTl {M' = M''} M⇒N) M≡M'NN = inj₁ (M'' ,p subst (λ x → x ⇒ M'') (appT-injl M≡M'NN) M⇒N ,p cong (appT M'') (appT-injr M≡M'NN))
APPl-⇒ (NN snoc _) (appTl M⇒N) M≡M'NN with APPl-⇒ NN M⇒N (appT-injl M≡M'NN)
APPl-⇒ (_ snoc _) (appTl _) M≡M'NN | inj₁ (M'' ,p M'⇒M'' ,p M₀≡M''NN) = inj₁ (M'' ,p M'⇒M'' ,p cong₂ appT M₀≡M''NN (appT-injr M≡M'NN))
APPl-⇒ (_ snoc _) (appTl _) _ | inj₂ M'isΛ = inj₂ M'isΛ
APPl-⇒ [] (impl _) ()
APPl-⇒ (_ snoc _) (impl _) ()
APPl-⇒ [] (impr _) ()
APPl-⇒ (_ snoc _) (impr _) ()
