module PHOML.Canon.Prop where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure.RST
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red

data CanonProp : Set where
  bot : CanonProp
  imp : CanonProp → CanonProp → CanonProp

decode : ∀ {V} → CanonProp → Term V
decode bot = ⊥
decode (imp φ ψ) = decode φ ⊃ decode ψ

decode-inj : ∀ {V θ θ'} → decode {V} θ ≡ decode θ' → θ ≡ θ'
decode-inj {θ = bot} {bot} _ = refl
decode-inj {θ = imp _ _} {bot} ()
decode-inj {θ = bot} {imp _ _} ()
decode-inj {θ = imp θ₁ θ₂} {imp θ₁' θ₂'} θ₁⊃θ₂≡θ₁'⊃θ₂' = cong₂ imp (decode-inj (⊃-injl θ₁⊃θ₂≡θ₁'⊃θ₂')) (decode-inj (⊃-injr θ₁⊃θ₂≡θ₁'⊃θ₂'))

canon-closed : ∀ {U V} (θ : CanonProp) {ρ : Rep U V} → decode θ 〈 ρ 〉 ≡ decode θ
canon-closed bot = refl
canon-closed (imp θ θ') = cong₂ _⊃_ (canon-closed θ) (canon-closed θ')

rep-red-canon : ∀ {U V} {φ : Term U} (θ : CanonProp) {ρ : Rep U V} →
  φ ↠ decode θ → φ 〈 ρ 〉 ↠ decode θ
rep-red-canon {U} {V} {φ} θ {ρ} φ↠θ = subst (λ x → φ 〈 ρ 〉 ↠ x) 
  (canon-closed θ) (↠-resp-rep φ↠θ)

canon-nf : ∀ {V θ} {φ : Term V} → decode θ ⇒ φ → Empty
canon-nf {θ = bot} ()
canon-nf {θ = imp φ _} (impl θ⇒φ) = canon-nf {θ = φ} θ⇒φ
canon-nf {θ = imp _ ψ} (impr θ⇒φ) = canon-nf {θ = ψ} θ⇒φ

canon-nf' : ∀ {V} θ {φ ψ : Term V} → φ ↠ ψ → decode θ ≡ φ → decode θ ≡ ψ
canon-nf' θ (inc φ⇒ψ) θ≡φ = ⊥-elim (canon-nf {θ = θ} (subst (λ x → x ⇒ _) (≡-sym θ≡φ) φ⇒ψ))
canon-nf' _ ref θ≡φ = θ≡φ
canon-nf' θ (trans φ↠ψ ψ↠ψ') θ≡φ = canon-nf' θ ψ↠ψ' (canon-nf' θ φ↠ψ θ≡φ)

red-canon : ∀ {V} {φ ψ : Term V} {θ : CanonProp} → φ ↠ decode θ → φ ≃ ψ → ψ ↠ decode θ
red-canon {V} {φ} {ψ} {θ} φ↠θ φ≃ψ = 
  let cr χ θ↠χ ψ↠χ = diamondRT-CR (λ _ _ _ → diamond) (decode θ) ψ (trans (sym (sub-RT-RST φ↠θ)) φ≃ψ) in 
  subst (λ x → ψ ↠ x) (≡-sym (canon-nf' θ θ↠χ refl)) ψ↠χ 

canon-unique : ∀ {V} {φ : Term V} {θ θ' : CanonProp} → φ ↠ decode θ → φ ↠ decode θ' → θ ≡ θ'
canon-unique {θ = θ} {θ'} φ↠θ φ↠θ' =
  let cr θ₀ θ↠θ₀ θ'↠θ₀ = diamond φ↠θ φ↠θ' in 
  decode-inj (≡-trans (canon-nf' θ θ↠θ₀ refl) (≡-sym (canon-nf' θ' θ'↠θ₀ refl)))

imp-red-imp : ∀ {V} {E F : Term V} → E ↠ F → Is-⊃ E → Is-⊃ F
imp-red-imp (inc (impl _)) is-⊃ = is-⊃
imp-red-imp (inc (impr _)) is-⊃ = is-⊃
imp-red-imp ref is⊃E = is⊃E
imp-red-imp (trans E↠F F↠G) is⊃E = imp-red-imp F↠G (imp-red-imp E↠F is⊃E)

imp-not-red-bot : ∀ {V} {φ ψ : Term V} → φ ⊃ ψ ↠ ⊥ → Empty
imp-not-red-bot φ⊃ψ↠⊥ with imp-red-imp φ⊃ψ↠⊥ is-⊃
imp-not-red-bot φ⊃ψ↠⊥ | ()

APPl-red-canon : ∀ {V M N} {NN : snocList (Term V)} {θ} → APPl (appT M N) NN ↠ decode θ → Reduces-to-Λ M
APPl-red-canon {NN = NN} Mx↠θ with APPl-red NN Mx↠θ refl
APPl-red-canon {NN = []} {θ = bot} _ | inj₁ (_ ,p _ ,p ())
APPl-red-canon {NN = _ snoc _} {θ = bot} _ | inj₁ (_ ,p _ ,p ())
APPl-red-canon {NN = []} {θ = imp _ _} _ | inj₁ (_ ,p _ ,p ())
APPl-red-canon {NN = _ snoc _} {θ = imp _ _} _ | inj₁ (_ ,p _ ,p ())
APPl-red-canon _ | inj₂ MrtΛ = MrtΛ

θps-red-ref : ∀ {V} (θ : CanonProp) → decode θ ⟦⟦ refSub ∶ idSub V ≡ idSub _ ⟧⟧ ↠ reff (decode θ)
θps-red-ref bot = ref
θps-red-ref (imp θ θ') = trans (↠-imp* (θps-red-ref θ) (θps-red-ref θ')) (inc ref⊃*)
