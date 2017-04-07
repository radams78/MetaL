module PHOML.Grammar.Const where
open import Data.Empty renaming (⊥ to Empty)
open import Prelims
open import PHOML.Grammar.Base
open PHOMLgrammar public
open import Grammar PHOML public

Proof : Alphabet → Set
Proof V = Expression V -vProof

Term : Alphabet → Set
Term V = Expression V -vTerm

Path : Alphabet → Set
Path V = Expression V -vPath

Equation : Alphabet → Set
Equation V = Expression V -nvEq

ty : ∀ {V} → Type → Expression V (nonVarKind -Type)
ty A = app (-ty A) []

⊥ : ∀ {V} → Term V
⊥ = app -bot []

infix 65 _⊃_
_⊃_ : ∀ {V} → Term V → Term V → Term V
φ ⊃ ψ = app -imp (φ ∷ (ψ ∷ []))

data Is-⊃ {V} : Term V → Set where
  is-⊃ : ∀ {φ} {ψ} → Is-⊃ (φ ⊃ ψ)

ΛT : ∀ {V} → Type → Term (V , -Term) → Term V
ΛT A M = app (-lamTerm A) (M ∷ [])

appT : ∀ {V} → Term V → Term V → Term V
appT M N = app -appTerm (M ∷ (N ∷ []))

ΛP : ∀ {V} → Term V → Proof (V , -Proof) → Proof V
ΛP φ δ = app -lamProof (φ ∷ (δ ∷ []))

appP : ∀ {V} → Proof V → Proof V → Proof V
appP δ ε = app -appProof (δ ∷ (ε ∷ []))

dir : ∀ {V} → Dir → Path V → Proof V
dir d P = app (-dir d) (P ∷ [])

plus : ∀ {V} → Path V → Proof V
plus P = dir -plus P

minus : ∀ {V} → Path V → Proof V
minus P = dir -minus P

reff : ∀ {V} → Term V → Path V
reff M = app -ref (M ∷ [])

infix 15 _⊃*_
_⊃*_ : ∀ {V} → Path V → Path V → Path V
P ⊃* Q = app -imp* (P ∷ (Q ∷ []))

univ : ∀ {V} → Term V → Term V → Proof V → Proof V → Path V
univ φ ψ P Q = app -univ (φ ∷ (ψ ∷ (P ∷ (Q ∷ []))))

λλλ : ∀ {V} → Type → Path (((V , -Term) , -Term) , -Path) → Path V
λλλ A P = app (-lll A) (P ∷ [])

app* : ∀ {V} → Term V → Term V → Path V → Path V → Path V
app* M N P Q = app -app* (M ∷ (N ∷ (P ∷ (Q ∷ []))))

infix 60 _≡〈_〉_
_≡〈_〉_ : ∀ {V} → Term V → Type → Term V → Equation V
M ≡〈 A 〉 N = app (-eq A) (M ∷ (N ∷ []))

infixl 59 _,T_
_,T_ : ∀ {V} → Context V → Type → Context (V , -Term)
Γ ,T A = Γ , ty A

infixl 59 _,P_
_,P_ : ∀ {V} → Context V → Term V → Context (V , -Proof)
_,P_ = _,_

infixl 59 _,E_
_,E_ : ∀ {V} → Context V → Equation V → Context (V , -Path)
_,E_ = _,_

yt : ∀ {V} → Expression V (nonVarKind -Type) → Type
yt (app (-ty A) []) = A

yt-rep : ∀ {U V} (A : Expression U -nvType) {ρ : Rep U V} → yt (A 〈 ρ 〉) ≡ yt A
yt-rep (app (-ty _) []) = refl

yt-sub : ∀ {U V} {A : Expression U -nvType} {σ : Sub U V} → yt (A ⟦ σ ⟧) ≡ yt A
yt-sub {A = app (-ty _) []} = refl

ty-yt : ∀ {V} {A : Expression V -nvType} → ty (yt A) ≡ A
ty-yt {A = app (-ty _) []} = refl

typeof' : ∀ {V} → Var V -Term → Context V → Type
typeof' x Γ  = yt (typeof x Γ)

APPl : ∀ {V} → Term V → snocList (Term V) → Term V
APPl M [] = M
APPl M (NN snoc N) = appT (APPl M NN) N

APPl-rep : ∀ {U V} {M : Term U} {NN : snocList (Term U)} {ρ : Rep U V} → (APPl M NN) 〈 ρ 〉 ≡ APPl (M 〈 ρ 〉) (snocmap (λ x → x 〈 ρ 〉) NN)
APPl-rep {NN = []} = refl
APPl-rep {NN = NN snoc N} {ρ} = cong (λ x → appT x (N 〈 ρ 〉)) (APPl-rep {NN = NN} {ρ})

type : ∀ {V} → Equation V → Type
type (app (-eq A) _) = A

type-rep : ∀ {U V} (E : Equation U) {ρ : Rep U V} → type (E 〈 ρ 〉) ≡ type E
type-rep (app (-eq _) _) = refl

left : ∀ {V} → Equation V → Term V
left (app (-eq _) (M ∷ (_ ∷ []))) = M

left-rep : ∀ {U V} (E : Equation U) {ρ : Rep U V} → left E 〈 ρ 〉 ≡ left (E 〈 ρ 〉)
left-rep (app (-eq _) (_ ∷ (_ ∷ []))) = refl

right : ∀ {V} → Equation V → Term V
right (app (-eq _) (_ ∷ (N ∷ []))) = N

right-rep : ∀ {U V} (E : Equation U) {ρ : Rep U V} → right E 〈 ρ 〉 ≡ right (E 〈 ρ 〉)
right-rep (app (-eq _) (_ ∷ (_ ∷ []))) = refl

id : ∀ {V} → Term V → Proof V
id φ = ΛP φ (var x₀)

-- Mx1...xn =/= Λ M' for n >= 1
APPl-not-Λ : ∀ {V M N} {NN : snocList (Term V)} {A M'} → APPl (appT M N) NN ≡ ΛT A M' → Empty
APPl-not-Λ {NN = []} ()
APPl-not-Λ {NN = _ snoc _} ()

APPP : ∀ {V} → Proof V → snocList (Proof V) → Proof V
APPP δ [] = δ
APPP δ (εε snoc ε) = appP (APPP δ εε) ε

APPP-rep : ∀ {U V} {δ : Proof U} {εε : snocList (Proof U)} {ρ : Rep U V} →
  APPP δ εε 〈 ρ 〉 ≡ APPP (δ 〈 ρ 〉) (snocmap (λ ε → ε 〈 ρ 〉) εε)
APPP-rep {εε = []} = refl
APPP-rep {εε = εε snoc ε} {ρ} = cong (λ x → appP x (ε 〈 ρ 〉)) (APPP-rep {εε = εε})
