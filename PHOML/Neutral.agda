module PHOML.Neutral where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.Red

data NeutralT : Alphabet → Set where

data NeutralE (V : Alphabet) : Set where
  var : Var V -Path → NeutralE V
  app*N : Term V → Term V → NeutralE V → Path V → NeutralE V
  imp*l : NeutralE V → Path V → NeutralE V
  imp*r : Path V → NeutralE V → NeutralE V

data NeutralP (V : Alphabet) : Set where
  var : Var V -Proof → NeutralP V
  app : NeutralP V → Proof V → NeutralP V
  dirN : Dir → NeutralE V → NeutralP V

decode-NeutralT : ∀ {V} → NeutralT V → Term V
decode-NeutralT ()

decode-NeutralE : ∀ {V} → NeutralE V → Path V
decode-NeutralE (var e) = var e
decode-NeutralE (app*N M N P Q) = app* M N (decode-NeutralE P) Q
decode-NeutralE (imp*l P Q) = decode-NeutralE P ⊃* Q
decode-NeutralE (imp*r P Q) = P ⊃* decode-NeutralE Q

decode-NeutralP : ∀ {V} → NeutralP V → Proof V
decode-NeutralP (var p) = var p
decode-NeutralP (app δ ε) = appP (decode-NeutralP δ) ε
decode-NeutralP (dirN d P) = dir d (decode-NeutralE P)

nrepE : ∀ {U V} → Rep U V → NeutralE U → NeutralE V
nrepE ρ (var e) = var (ρ -Path e)
nrepE ρ (app*N M N ν P) = app*N (M 〈 ρ 〉) (N 〈 ρ 〉) (nrepE ρ ν) (P 〈 ρ 〉)
nrepE ρ (imp*l P Q) = imp*l (nrepE ρ P) (Q 〈 ρ 〉)
nrepE ρ (imp*r P Q) = imp*r (P 〈 ρ 〉) (nrepE ρ Q)

decode-nrepE : ∀ {U V} {ρ : Rep U V} (ν : NeutralE U) → decode-NeutralE (nrepE ρ ν) ≡ decode-NeutralE ν 〈 ρ 〉
decode-nrepE (var e) = refl
decode-nrepE {ρ = ρ} {app*N M N ν P} = cong (λ x → app* (M 〈 ρ 〉) (N 〈 ρ 〉) x (P 〈 ρ 〉)) (decode-nrepE ν)
decode-nrepE {ρ = ρ} {imp*l P Q} = cong (λ x → x ⊃* Q 〈 ρ 〉) (decode-nrepE P)
decode-nrepE {ρ = ρ} {imp*r P Q} = cong (λ x → P 〈 ρ 〉 ⊃* x) (decode-nrepE Q)

nrepP : ∀ {U V} → Rep U V → NeutralP U → NeutralP V
nrepP ρ (var p) = var (ρ _ p)
nrepP ρ (app ν δ) = app (nrepP ρ ν) (δ 〈 ρ 〉)
nrepP ρ (dirN d P) = dirN d (nrepE ρ P)

decode-nrepP : ∀ {U V} {ρ : Rep U V} {ν : NeutralP U} → decode-NeutralP (nrepP ρ ν) ≡ decode-NeutralP ν 〈 ρ 〉
decode-nrepP {ρ = ρ} {ν = var p} = refl
decode-nrepP {ρ = ρ} {ν = app ν δ} = cong (λ x → appP x (δ 〈 ρ 〉)) (decode-nrepP {ρ = ρ} {ν = ν})
decode-nrepP {ν = dirN d P} = cong (dir d) (decode-nrepE P)

reflect-NeutralE : ∀ {U V} (P : Path U) (Q : NeutralE V) (ρ : Rep U V) →
  P 〈 ρ 〉 ≡ decode-NeutralE Q → Σ[ P' ∈ NeutralE U ] P ≡ decode-NeutralE P'
reflect-NeutralE (var e) (var _) _ _ = var e ,p refl
reflect-NeutralE (var _) (app*N _ _ _ _) _ ()
reflect-NeutralE (var _) (imp*l _ _) _ ()
reflect-NeutralE (var _) (imp*r _ _) _ ()
reflect-NeutralE (app -ref _) (var _) _ ()
reflect-NeutralE (app -ref _) (app*N _ _ _ _) _ ()
reflect-NeutralE (app -ref _) (imp*l _ _) _ ()
reflect-NeutralE (app -ref _) (imp*r _ _) _ ()
reflect-NeutralE (app -imp* _) (var _) _ ()
reflect-NeutralE (app -imp* _) (app*N _ _ _ _) _ ()
reflect-NeutralE (app -imp* (P ∷ (Q ∷ []))) (imp*l P' Q') ρ Pρ≡Q = 
  let P₀ ,p P₀≡P = reflect-NeutralE (P) (P') ρ (⊃*-injl Pρ≡Q) in
  imp*l P₀ Q ,p cong (λ x → x ⊃* Q) P₀≡P
reflect-NeutralE (app -imp* (P ∷ (Q ∷ []))) (imp*r P' Q') ρ Pρ≡Q = 
  let Q₀ ,p Q₀≡Q = reflect-NeutralE (Q) (Q') ρ (⊃*-injr Pρ≡Q) in 
  imp*r P Q₀ ,p cong (λ x → P ⊃* x) Q₀≡Q
reflect-NeutralE (app -univ _) (var _) _ ()
reflect-NeutralE (app -univ _) (app*N _ _ _ _) _ ()
reflect-NeutralE (app -univ _) (imp*l P Q) _ ()
reflect-NeutralE (app -univ _) (imp*r P Q) _ ()
reflect-NeutralE (app (-lll _) _) (var _) _ ()
reflect-NeutralE (app (-lll _) _) (app*N _ _ _ _) _ ()
reflect-NeutralE (app (-lll _) _) (imp*l P Q) _ ()
reflect-NeutralE (app (-lll _) _) (imp*r P Q) _ ()
reflect-NeutralE (app -app* _) (var _) _ ()
reflect-NeutralE (app -app* (M₁ ∷ (M₂ ∷ (P₁ ∷ (P₂ ∷ []))))) (app*N N₁ N₂ Q₁ Q₂) (ρ) Pρ≡Q = 
  let P₁' ,p P₁≡P₁' = reflect-NeutralE P₁ Q₁ ρ (app*-injl Pρ≡Q) in
  (app*N M₁ M₂ P₁' P₂) ,p (cong (λ x → app* M₁ M₂ x P₂) P₁≡P₁')
reflect-NeutralE (app -app* _) (imp*l P Q) _ ()
reflect-NeutralE (app -app* _) (imp*r P Q) _ ()

reflect-NeutralP : ∀ {U V} (δ : Proof U) (χ : NeutralP V) {ρ : Rep U V} → δ 〈 ρ 〉 ≡ decode-NeutralP χ → Σ[ χ' ∈ NeutralP U ] δ ≡ decode-NeutralP χ'
reflect-NeutralP (var x) _ _ = var x ,p refl
reflect-NeutralP (app _ _) (var _) ()
reflect-NeutralP (app -lamProof x₁) (app χ x₂) ()
reflect-NeutralP (app -appProof (δ ∷ (ε ∷ []))) (app χ ε') δρ≡χ =
  let χ' ,p χ'ρ≡χ = reflect-NeutralP δ χ (appP-injl δρ≡χ) in 
  app χ' ε ,p cong (λ x → appP x ε) χ'ρ≡χ
reflect-NeutralP (app (-dir x) x₁) (app χ x₂) ()
reflect-NeutralP (app -lamProof x₁) (dirN x₂ x₃) ()
reflect-NeutralP (app -appProof x₁) (dirN x₂ x₃) ()
reflect-NeutralP (app (-dir d) (P ∷ [])) (dirN _ Q) {ρ} δρ≡χ = 
  let χ' ,p δ≡χ' = reflect-NeutralE P Q ρ (dir-inj δρ≡χ) in
  dirN d χ' ,p cong (dir d) δ≡χ'

neutralE-osr : ∀ {V} (P : NeutralE V) {Q} → decode-NeutralE P ⇒ Q →
  Σ[ Q' ∈ NeutralE V ] Q ≡ decode-NeutralE Q'
neutralE-osr (var _) ()
neutralE-osr (app*N _ _ (var _) _) (app*l ())
neutralE-osr (app*N M M' (app*N N N' P P') Q) (app*l P⇒Q) = 
  let Q' ,p Q≡Q' = neutralE-osr (app*N N N' P P') P⇒Q in
  app*N M M' Q' Q ,p (cong (λ x → app* M M' x Q) Q≡Q')
neutralE-osr (app*N M M' (imp*l P P') Q) (app*l P⇒Q) =
  let Q' ,p Q≡Q' = neutralE-osr (imp*l P P') P⇒Q in
  app*N M M' Q' Q ,p (cong (λ x → app* M M' x Q) Q≡Q')
neutralE-osr (app*N M M' (imp*r P P') Q) (app*l P⇒Q) =
  let Q' ,p Q≡Q' = neutralE-osr (imp*r P P') P⇒Q in
  app*N M M' Q' Q ,p (cong (λ x → app* M M' x Q) Q≡Q')
neutralE-osr (imp*l (var _) _) (imp*l ())
neutralE-osr (imp*l (var x) _) (imp*r _) = imp*l (var x) _ ,p refl
neutralE-osr (imp*l (app*N M M' P P') Q) (imp*l P⇒Q) = 
  let P' ,p P≡P' = neutralE-osr (app*N M M' P P') P⇒Q in
  imp*l P' Q ,p cong (λ x → x ⊃* Q) P≡P'
neutralE-osr (imp*l (app*N M M' P P') Q) (imp*r P⇒Q) =
  imp*l (app*N M M' P P') _ ,p refl
neutralE-osr (imp*l (imp*l P P') Q) (imp*l Q⇒Q') =
  let P' ,p P≡P' = neutralE-osr (imp*l P P') Q⇒Q' in
  imp*l P' Q ,p cong (λ x → x ⊃* Q) P≡P'
neutralE-osr (imp*l (imp*l P P') Q) (imp*r P⇒Q) =
  imp*l (imp*l P P') _ ,p refl
neutralE-osr (imp*l (imp*r P P') Q) (imp*l PP'⇒P₀) =
  let P₀ ,p P₀≡P₀ = neutralE-osr (imp*r P P') PP'⇒P₀ in
  imp*l P₀ Q ,p cong (λ x → x ⊃* Q) P₀≡P₀
neutralE-osr (imp*l (imp*r P P') Q) (imp*r P⇒Q) =
  imp*l (imp*r P P') _ ,p refl
neutralE-osr (imp*r _ (var x)) (imp*l _) = (imp*r _ (var x)) ,p refl
neutralE-osr (imp*r _ (var _)) (imp*r ())
neutralE-osr (imp*r _ (app*N M N Q Q')) (imp*l _) =
  imp*r _ (app*N M N Q Q') ,p refl
neutralE-osr (imp*r P (app*N M N Q Q')) (imp*r QQ'⇒Q₀) =
  let Q₀ ,p Q₀≡Q₀ = neutralE-osr (app*N M N Q Q') QQ'⇒Q₀ in
  imp*r P Q₀ ,p (cong (λ x → P ⊃* x) Q₀≡Q₀)
neutralE-osr (imp*r _ (imp*l Q Q')) (imp*l _) =
  imp*r _ (imp*l Q Q') ,p refl
neutralE-osr (imp*r P (imp*l Q Q')) (imp*r Q⊃*Q'⇒Q₀) =
  let Q₀ ,p Q₀≡Q₀ = neutralE-osr (imp*l Q Q') Q⊃*Q'⇒Q₀ in
  imp*r P Q₀ ,p (cong (λ x → P ⊃* x) Q₀≡Q₀)
neutralE-osr (imp*r _ (imp*r Q Q')) (imp*l _) =
  imp*r _ (imp*r Q Q') ,p refl
neutralE-osr (imp*r P (imp*r Q Q')) (imp*r Q⊃*Q'⇒Q₀) =
  let Q₀ ,p Q₀≡Q₀ = neutralE-osr (imp*r Q Q') Q⊃*Q'⇒Q₀ in
  imp*r P Q₀ ,p (cong (λ x → P ⊃* x) Q₀≡Q₀)

neutralP-red : ∀ {V} {δ ε} (ν : NeutralP V) → δ ↠ ε → δ ≡ decode-NeutralP ν →
  Σ[ ν' ∈ NeutralP V ] ε ≡ decode-NeutralP ν'
neutralP-red (var _) (inc βP) ()
neutralP-red (app (var _) _) (inc βP) ()
neutralP-red (app (app _ _) _) (inc βP) ()
neutralP-red (app (dirN _ _) _) (inc βP) ()
neutralP-red (dirN _ _) (inc βP) ()
neutralP-red (var _) (inc refdir) ()
neutralP-red (app _ _) (inc refdir) ()
neutralP-red (dirN _ (var _)) (inc refdir) ()
neutralP-red (dirN _ (app*N _ _ _ _)) (inc refdir) ()
neutralP-red (dirN _ (imp*l _ _)) (inc refdir) ()
neutralP-red (dirN _ (imp*r _ _)) (inc refdir) ()
neutralP-red (var _) (inc (appPl _)) ()
neutralP-red (app ν ε) (inc (appPl {δ' = ν'} ν⇒ν')) δ≡νε = 
  let ν₀' ,p ν'≡ν₀' = neutralP-red (ν) (inc ν⇒ν') (appP-injl δ≡νε) in app ν₀' ε ,p cong₂ appP ν'≡ν₀' (appP-injr δ≡νε)
neutralP-red (dirN _ _) (inc (appPl _)) ()
neutralP-red (var _) (inc univplus) ()
neutralP-red (app _ _) (inc univplus) ()
neutralP-red (dirN _ (var _)) (inc univplus) ()
neutralP-red (dirN _ (app*N _ _ _ _)) (inc univplus) ()
neutralP-red (dirN _ (imp*l _ _)) (inc univplus) ()
neutralP-red (dirN _ (imp*r _ _)) (inc univplus) ()
neutralP-red (var _) (inc univminus) ()
neutralP-red (app _ _) (inc univminus) ()
neutralP-red (dirN _ (var _)) (inc univminus) ()
neutralP-red (dirN _ (app*N _ _ _ _)) (inc univminus) ()
neutralP-red (dirN _ (imp*l _ _)) (inc univminus) ()
neutralP-red (dirN _ (imp*r _ _)) (inc univminus) ()
neutralP-red (var _) (inc (dirR _)) ()
neutralP-red (app (var _) _) (inc (dirR _)) ()
neutralP-red (app (app _ _) _) (inc (dirR _)) ()
neutralP-red (app (dirN _ _) _) (inc (dirR _)) ()
neutralP-red (dirN d P) (inc (dirR {Q = Q} P⇒Q)) refl = 
  let Q' ,p Q'≡Q = neutralE-osr P P⇒Q in 
  dirN d Q' ,p cong (dir d) Q'≡Q
neutralP-red (ν) ref δ≡ν = ν ,p δ≡ν
neutralP-red (ν) (trans δ↠ε ε↠ε') δ≡ν =
  let ν₂ ,p ε≡ν₂ = neutralP-red (ν) δ↠ε δ≡ν in 
  neutralP-red ν₂ ε↠ε' ε≡ν₂

NeutralE-not-closed : NeutralE ∅ → Empty
NeutralE-not-closed (var ())
NeutralE-not-closed (app*N _ _ N _) = NeutralE-not-closed N
NeutralE-not-closed (imp*l N _) = NeutralE-not-closed N
NeutralE-not-closed (imp*r _ N) = NeutralE-not-closed N

NeutralP-not-closed : NeutralP ∅ → Empty
NeutralP-not-closed (var ())
NeutralP-not-closed (app N _) = NeutralP-not-closed N
NeutralP-not-closed (dirN _ N) = NeutralE-not-closed N
