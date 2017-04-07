module PHOML.Grammar.Inj where
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Prelims.Snoclist
open import PHOML.Grammar.Const

⇛-injl : ∀ {A A' B B' : Type} → A ⇛ B ≡ A' ⇛ B' → A ≡ A'
⇛-injl refl = refl

⇛-injr : ∀ {A A' B B' : Type} → A ⇛ B ≡ A' ⇛ B' → B ≡ B'
⇛-injr refl = refl

⊃-injl : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → φ ≡ φ'
⊃-injl refl = refl

⊃-injr : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≡ φ' ⊃ ψ' → ψ ≡ ψ'
⊃-injr refl = refl

appT-injl : ∀ {V} {M M' N N' : Term V} → appT M N ≡ appT M' N' → M ≡ M'
appT-injl refl = refl

appT-injr : ∀ {V} {M N P Q : Term V} → appT M N ≡ appT P Q → N ≡ Q
appT-injr refl = refl

appP-injl : ∀ {V} {δ δ' ε ε' : Proof V} → appP δ ε ≡ appP δ' ε' → δ ≡ δ'
appP-injl refl = refl

appP-injr : ∀ {V} {δ δ' ε ε' : Proof V} → appP δ ε ≡ appP δ' ε' → ε ≡ ε'
appP-injr refl = refl

app*-inj₁ : ∀ {V} {M M' N N' : Term V} {P P' Q Q'} → app* M N P Q ≡ app* M' N' P' Q' → M ≡ M'
app*-inj₁ refl = refl

app*-inj₂ : ∀ {V} {M M' N N' : Term V} {P P' Q Q' : Path V} → app* M N P Q ≡ app* M' N' P' Q' → N ≡ N'
app*-inj₂ refl = refl

app*-injl : ∀ {V} {M M' N N' : Term V} {P P' Q Q' : Path V} → app* M N P Q ≡ app* M' N' P' Q' → P ≡ P'
app*-injl refl = refl

app*-injr : ∀ {V} {M M' N N' : Term V} {P P' Q Q' : Path V} → app* M N P Q ≡ app* M' N' P' Q' → Q ≡ Q'
app*-injr refl = refl

eq-inj₁ : ∀ {V A A'} {M M' N N' : Term V} → M ≡〈 A 〉 N ≡ M' ≡〈 A' 〉 N' → M ≡ M'
eq-inj₁ refl = refl

eq-inj₂ : ∀ {V} {M N M' N' : Term V} {A A'} → M ≡〈 A 〉 N ≡ M' ≡〈 A' 〉 N' → A ≡ A'
eq-inj₂ refl = refl

eq-inj₃ : ∀ {V} {M N M' N' : Term V} {A A'} → M ≡〈 A 〉 N ≡ M' ≡〈 A' 〉 N' → N ≡ N'
eq-inj₃ refl = refl

dir-inj : ∀ {V} {P Q : Path V} {d d'} → dir d P ≡ dir d' Q → P ≡ Q
dir-inj refl = refl

univ-injl : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε' : Proof V} →
  univ φ ψ δ ε ≡ univ φ' ψ' δ' ε' → δ ≡ δ'
univ-injl refl = refl

⊃*-injl : ∀ {V} {P P' Q Q' : Path V} → P ⊃* Q ≡ P' ⊃* Q' → P ≡ P'
⊃*-injl refl = refl

⊃*-injr : ∀ {V} {P P' Q Q' : Path V} → P ⊃* Q ≡ P' ⊃* Q' → Q ≡ Q'
⊃*-injr refl = refl

λλλ-injl : ∀ {V A A'} {P P' : Path (extend V pathDom)} → λλλ A P ≡ λλλ A' P' → A ≡ A'
λλλ-injl refl = refl

-- If Mx1...xn = (Λ M') N with n >= 1 then M = Λ M'
APPl-Λ : ∀ {V M N} {NN : snocList (Term V)} {A M' N'} →
  APPl (appT M N) NN ≡ appT (ΛT A M') N' → M ≡ ΛT A M'
APPl-Λ {NN = []} Mx≡ΛM'N = appT-injl Mx≡ΛM'N
APPl-Λ {NN = NN snoc _} Mx≡ΛM'N = ⊥-elim (APPl-not-Λ {NN = NN} (appT-injl Mx≡ΛM'N))
