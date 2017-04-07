module PHOML.Red.Reflect where
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RTRed

⇒-reflect-rep : ∀ {U V K} {E : VExpression U K} {ρ : Rep U V} {F} → E 〈 ρ 〉 ⇒ F → Σ[ F' ∈ VExpression U K ] (E ⇒ F' × F ≡ F' 〈 ρ 〉)
⇒-reflect-rep {E = var _} ()
⇒-reflect-rep {E = app -bot []} ()
⇒-reflect-rep {E = app -imp (φ ∷ (ψ ∷ []))} {ρ} (impl φρ⇒φ'ρ) = 
  let φ' ,p φ⇒φ' ,p φ'ρ≡φ'ρ = ⇒-reflect-rep φρ⇒φ'ρ in 
  φ' ⊃ ψ ,p impl φ⇒φ' ,p cong (λ x → x ⊃ ψ 〈 ρ 〉) φ'ρ≡φ'ρ
⇒-reflect-rep {E = app -imp (φ ∷ (ψ ∷ []))} {ρ} (impr ψρ⇒ψ'ρ) =
  let ψ' ,p ψ⇒ψ' ,p ψ'ρ≡ψ'ρ = ⇒-reflect-rep ψρ⇒ψ'ρ in 
  φ ⊃ ψ' ,p impr ψ⇒ψ' ,p cong (λ x → φ 〈 ρ 〉 ⊃ x) ψ'ρ≡ψ'ρ
⇒-reflect-rep {E = app (-lamTerm _) _} ()
⇒-reflect-rep {E = app -appTerm (var _ ∷ (_ ∷ []))} (appTl ())
⇒-reflect-rep {E = app -appTerm (app -bot [] ∷ (_ ∷ []))} (appTl ())
⇒-reflect-rep {E = app -appTerm (app -imp (φ ∷ (ψ ∷ [])) ∷ (N ∷ []))} {ρ} (appTl Mρ⇒M'ρ) = 
  let M' ,p M⇒M' ,p M'ρ≡M'ρ = ⇒-reflect-rep Mρ⇒M'ρ in
  appT M' N ,p appTl M⇒M' ,p cong (λ x → appT x (N 〈 ρ 〉)) M'ρ≡M'ρ
⇒-reflect-rep {E = app -appTerm (app (-lamTerm A) (M ∷ []) ∷ (N ∷ []))} βT = 
  M ⟦ x₀:= N ⟧ ,p βT ,p (≡-sym (•RS-botSub M))
⇒-reflect-rep {E = app -appTerm (app (-lamTerm A) (M ∷ []) ∷ (N ∷ []))} (appTl ())
⇒-reflect-rep {E = app -appTerm (app -appTerm x₁ ∷ (N ∷ []))} {ρ} (appTl Mρ⇒M'ρ) =
  let M' ,p M⇒M' ,p M'ρ≡M'ρ = ⇒-reflect-rep Mρ⇒M'ρ in
  appT M' N ,p appTl M⇒M' ,p cong (λ x → appT x (N 〈 ρ 〉)) M'ρ≡M'ρ
⇒-reflect-rep {E = app -lamProof _} ()
⇒-reflect-rep {E = app -appProof (var _ ∷ (_ ∷ []))} (appPl ())
⇒-reflect-rep {E = app -appProof (app -lamProof (φ ∷ (δ ∷ [])) ∷ (ε ∷ []))} βP = (δ ⟦ x₀:= ε ⟧) ,p (βP ,p (≡-sym (•RS-botSub δ)))
⇒-reflect-rep {E = app -appProof (app -lamProof (φ ∷ (δ ∷ [])) ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app -appProof x₁ ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (var _ ∷ []) ∷ (ε ∷ []))} {ρ} (appPl (dirR ()))
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -ref (M ∷ []) ∷ []) ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -imp* x₁ ∷ []) ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -univ x₁ ∷ []) ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app (-lll x) x₁ ∷ []) ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app -appProof (app (-dir _) (app -app* x₁ ∷ []) ∷ (ε ∷ []))} {ρ} (appPl δρ⇒δ'ρ) =
  let δ' ,p δ⇒δ' ,p δ'ρ≡δ'ρ = ⇒-reflect-rep δρ⇒δ'ρ in
  appP δ' ε ,p appPl δ⇒δ' ,p cong (λ x → appP x (ε 〈 ρ 〉)) δ'ρ≡δ'ρ
⇒-reflect-rep {E = app (-dir _) (var _ ∷ [])} (dirR ())
⇒-reflect-rep {E = app (-dir _) (app -ref (_ ∷ []) ∷ [])} refdir = _ ,p refdir ,p refl
⇒-reflect-rep {E = app (-dir _) (app -ref (_ ∷ []) ∷ [])} (dirR ())
⇒-reflect-rep {E = app (-dir _) (app -imp* _ ∷ [])} (dirR Mρ⇒N') =
  let N ,p M⇒N ,p Nρ≡N' = ⇒-reflect-rep Mρ⇒N' in
  _ ,p dirR M⇒N ,p cong (dir _) Nρ≡N'
⇒-reflect-rep {E = app (-dir .-plus) (app -univ (φ ∷ (ψ ∷ (δ ∷ (ε ∷ [])))) ∷ [])} univplus = _ ,p univplus ,p refl
⇒-reflect-rep {E = app (-dir .-minus) (app -univ (φ ∷ (ψ ∷ (δ ∷ (ε ∷ [])))) ∷ [])} univminus = _ ,p univminus ,p refl
⇒-reflect-rep {E = app (-dir _) (app -univ (φ ∷ (ψ ∷ (δ ∷ (ε ∷ [])))) ∷ [])} (dirR ())
⇒-reflect-rep {E = app (-dir _) (app (-lll _) _ ∷ [])} (dirR ())
⇒-reflect-rep {E = app (-dir _) (app -app* _ ∷ [])} (dirR Mρ⇒N') =
  let N ,p M⇒N ,p Nρ≡N' = ⇒-reflect-rep Mρ⇒N' in
  _ ,p dirR M⇒N ,p cong (dir _) Nρ≡N'
⇒-reflect-rep {E = app -ref _} ()
⇒-reflect-rep {E = app -imp* (var x ∷ (Q ∷ []))} (imp*l ())
⇒-reflect-rep {E = app -imp* (var x ∷ (Q ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  var x ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → var (ρ _ x) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ (var x ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* var x ,p imp*l P⇒P' ,p cong (λ y → y ⊃* var (ρ _ x)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ (var _ ∷ []))} (imp*r ())
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app -ref (N ∷ []) ∷ []))} ref⊃* = 
  reff (M ⊃ N) ,p ref⊃* ,p refl
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app -ref (N ∷ []) ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* reff N ,p imp*l P⇒P' ,p cong (λ y → y ⊃* reff (N 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app -ref (N ∷ []) ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ (app -imp* (Q₁ ∷ (Q₂ ∷ [])) ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* (Q₁ ⊃* Q₂) ,p imp*l P⇒P' ,p cong (λ y → y ⊃* (Q₁ 〈 ρ 〉 ⊃* Q₂ 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app -imp* x₂ ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ (app -univ (φ ∷ (ψ ∷ (δ ∷ (ε ∷ [])))) ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* univ φ ψ δ ε ,p imp*l P⇒P' ,p cong (λ y → y ⊃* univ (φ 〈 ρ 〉) (ψ 〈 ρ 〉) (δ 〈 ρ 〉) (ε 〈 ρ 〉)) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (φ ∷ []) ∷ (app -univ (ψ ∷ (ψ' ∷ (δ ∷ (ε ∷ [])))) ∷ []))} {ρ} ref⊃*univ = _ ,p ref⊃*univ ,p (cong₂ (univ _ _) 
  (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP (≡-sym (liftRep-upRep₂ δ)) refl))) 
  (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP (≡-sym (liftRep-upRep₂ ε)) refl))))
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app -univ x₂ ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref _ ∷ (app (-lll A) (Q ∷ []) ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* λλλ A Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* (λλλ A Q) 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app (-lll x) x₂ ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -ref x₁ ∷ (app -app* (M ∷ (N ∷ (Q₁ ∷ (Q₂ ∷ [])))) ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* app* M N Q₁ Q₂ ,p imp*l P⇒P' ,p cong (λ y → y ⊃* (app* M N Q₁ Q₂) 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -ref (M ∷ []) ∷ (app -app* _ ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  reff M ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → reff (M 〈 ρ 〉) ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -imp* _ ∷ (Q ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -imp* (P₁ ∷ (P₂ ∷ [])) ∷ (Q ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  (P₁ ⊃* P₂) ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (P₁ ⊃* P₂) 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -univ (φ ∷ (φ' ∷ (δ ∷ (ε ∷ [])))) ∷ (app -ref (N ∷ []) ∷ []))} {ρ} univ⊃*ref = _ ,p (univ⊃*ref ,p (cong₂ (univ _ _) 
  (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ')) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ ε)) refl)))) 
  (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ δ)) refl))))))
⇒-reflect-rep {E = app -imp* (app -univ (φ ∷ (ψ ∷ (δ ∷ (ε ∷ [])))) ∷ (app -univ (φ' ∷ (ψ' ∷ (δ' ∷ (ε' ∷ [])))) ∷ []))} {ρ} univ⊃*univ = _ ,p univ⊃*univ ,p 
  (cong₂ (univ _ _) 
    (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep ψ)) (cong₂ appP (≡-sym (liftRep-upRep₂ δ')) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ ε)) refl))))) 
    (cong₂ ΛP refl (cong₂ ΛP (≡-sym (liftRep-upRep φ)) (cong₂ appP (≡-sym (liftRep-upRep₂ ε')) (cong₂ appP refl (cong₂ appP (≡-sym (liftRep-upRep₂ δ)) refl))))))
⇒-reflect-rep {E = app -imp* (app -univ _ ∷ (Q ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -univ (φ ∷ (ψ ∷ (δ ∷ (ε ∷ [])))) ∷ (Q ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  (univ φ ψ δ ε) ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (univ φ ψ δ ε) 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app (-lll x) x₁ ∷ (Q ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app (-lll A) (P ∷ []) ∷ (Q ∷ []))} {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  λλλ A P ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (λλλ A P) 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -imp* (app -app* x₁ ∷ (Q ∷ []))} {ρ} (imp*l Pρ⇒P'ρ) =
  let P' ,p P⇒P' ,p P'ρ≡P'ρ = ⇒-reflect-rep Pρ⇒P'ρ in
  P' ⊃* Q ,p imp*l P⇒P' ,p cong (λ y → y ⊃* Q 〈 ρ 〉) P'ρ≡P'ρ
⇒-reflect-rep {E = app -imp* (app -app* (M ∷ (N ∷ (P ∷ (P' ∷ [])))) ∷ (Q ∷ []))}  {ρ} (imp*r Qρ⇒Q'ρ) =
  let Q' ,p Q⇒Q' ,p Q'ρ≡Q'ρ = ⇒-reflect-rep Qρ⇒Q'ρ in
  app* M N P P' ⊃* Q' ,p imp*r Q⇒Q' ,p cong (λ y → (app* M N P P') 〈 ρ 〉 ⊃* y) Q'ρ≡Q'ρ
⇒-reflect-rep {E = app -univ _} ()
⇒-reflect-rep {E = app (-lll _) _} ()
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (var _ ∷ (_ ∷ []))))} (app*l ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (var _ ∷ []) ∷ (_ ∷ []))))} (app*l ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (var _ ∷ []) ∷ (_ ∷ []))))} (reffR ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -bot _ ∷ []) ∷ (_ ∷ []))))} (app*l ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -bot _ ∷ []) ∷ (_ ∷ []))))} (reffR ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -imp _ ∷ []) ∷ (_ ∷ []))))} (app*l ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -imp (_ ∷ (_ ∷ [])) ∷ []) ∷ (_ ∷ []))))} (reffR (impl φρ⇒φ')) =
  let φ' ,p φ⇒φ' ,p φ'ρ≡φ' = ⇒-reflect-rep φρ⇒φ' in 
  _ ,p reffR (impl φ⇒φ') ,p cong₄ app* refl refl (cong reff (cong₂ _⊃_ φ'ρ≡φ' refl)) refl
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -imp (_ ∷ (_ ∷ [])) ∷ []) ∷ (_ ∷ []))))} (reffR (impr ψρ⇒ψ')) =
  let ψ' ,p ψ⇒ψ' ,p ψ'ρ≡ψ' = ⇒-reflect-rep ψρ⇒ψ' in
  _ ,p reffR (impr ψ⇒ψ') ,p cong₄ app* refl refl (cong reff (cong₂ _⊃_ refl ψ'ρ≡ψ')) refl
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app (-lamTerm _) (M ∷ []) ∷ []) ∷ (_ ∷ []))))} βPP = _ ,p βPP ,p (≡-sym (botPathSub-liftRep {M = M}))
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app (-lamTerm _) (_ ∷ []) ∷ []) ∷ (_ ∷ []))))} (app*l ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app (-lamTerm _) (_ ∷ []) ∷ []) ∷ (_ ∷ []))))} (reffR ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -appTerm _ ∷ []) ∷ (_ ∷ []))))} (app*l ())
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -ref (app -appTerm (_ ∷ (_ ∷ [])) ∷ []) ∷ (_ ∷ []))))} (reffR Eρ⇒F) =
  let F' ,p E⇒F' ,p F'ρ≡F = ⇒-reflect-rep Eρ⇒F in 
  _ ,p reffR E⇒F' ,p cong₄ app* refl refl (cong reff F'ρ≡F) refl
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -imp* _ ∷ (_ ∷ []))))} (app*l Eρ⇒F) =
  let F' ,p E⇒F' ,p F'ρ≡F = ⇒-reflect-rep Eρ⇒F in 
  _ ,p app*l E⇒F' ,p cong₄ app* refl refl F'ρ≡F refl
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app -univ _ ∷ (_ ∷ []))))} (app*l Eρ⇒F) =
  let F' ,p E⇒F' ,p F'ρ≡F = ⇒-reflect-rep Eρ⇒F in 
  _ ,p app*l E⇒F' ,p cong₄ app* refl refl F'ρ≡F refl
⇒-reflect-rep {E = app -app* (_ ∷ (_ ∷ (app (-lll _) (P ∷ []) ∷ (_ ∷ []))))} βE = 
  _ ,p βE ,p botSub₃-liftRep₃ P
⇒-reflect-rep {E = app -app* (M ∷ (N ∷ (app (-lll A) (P ∷ []) ∷ (Q ∷ []))))} (app*l Eρ⇒F) =
  let F' ,p E⇒F' ,p F'ρ≡F = ⇒-reflect-rep Eρ⇒F in 
  _ ,p app*l E⇒F' ,p cong₄ app* refl refl F'ρ≡F refl
⇒-reflect-rep {E = app -app* (M ∷ (N ∷ (app -app* x₁ ∷ (Q ∷ []))))} (app*l Eρ⇒F) =
  let F' ,p E⇒F' ,p F'ρ≡F = ⇒-reflect-rep Eρ⇒F in 
  _ ,p app*l E⇒F' ,p cong₄ app* refl refl F'ρ≡F refl

↠-reflect-rep : ∀ {U V K} {E : VExpression U K} {ρ : Rep U V} {E' F'} → E' ↠ F' → E 〈 ρ 〉 ≡ E' → Σ[ F ∈ VExpression U K ] (E ↠ F × F 〈 ρ 〉 ≡ F')
↠-reflect-rep {F' = F'} (inc E'⇒F') Eρ≡E' = 
  let F ,p E⇒F ,p F'≡Fρ = ⇒-reflect-rep (subst (λ x → x ⇒ F') (≡-sym Eρ≡E') E'⇒F') in
  F ,p inc E⇒F ,p ≡-sym F'≡Fρ
↠-reflect-rep ref Eρ≡E' = _ ,p ref ,p Eρ≡E'
↠-reflect-rep (trans E'↠F' F'↠G') Eρ≡E' = 
  let F ,p E↠F ,p Fρ≡F' = ↠-reflect-rep E'↠F' Eρ≡E' in
  let G ,p F↠G ,p Gρ≡G' = ↠-reflect-rep F'↠G' Fρ≡F' in
  G ,p trans E↠F F↠G ,p Gρ≡G'
