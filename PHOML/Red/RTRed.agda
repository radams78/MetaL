module PHOML.Red.RTRed where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Bool
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RRed

infix 10 _↠_
_↠_ : ∀ {V K} → Expression V K → Expression V K → Set
_↠_ {V} {K} = RTClose (_⇒_ {V} {K})

↠-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ↠ F → E 〈 ρ 〉 ↠ F 〈 ρ 〉
↠-resp-rep = respects-RT (λ _ _ → ⇒-resp-rep) _ _

↠-resp-ps : ∀ {U V} {M N : Term U} {τ : PathSub U V} {ρ σ} → M ↠ N → M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ↠ N ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧
↠-resp-ps = respects-RT (λ _ _ → ⇒-resp-ps) _ _

↠-impl : ∀ {V} {φ φ' ψ : Term V} → φ ↠ φ' → φ ⊃ ψ ↠ φ' ⊃ ψ
↠-impl = respects-RT (λ _ _ → impl) _ _

↠-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ↠ ψ' → φ ⊃ ψ ↠ φ ⊃ ψ'
↠-impr = respects-RT (λ _ _ → impr) _ _

↠-imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ↠ φ' → ψ ↠ ψ' → φ ⊃ ψ ↠ φ' ⊃ ψ'
↠-imp φ↠φ' ψ↠ψ' = trans (↠-impl φ↠φ') (↠-impr ψ↠ψ')

↠-appT : ∀ {V} {M M' N : Term V} → M ↠ M' → appT M N ↠ appT M' N
↠-appT = respects-RT (λ _ _ → appTl) _ _

↠-appP : ∀ {V} {δ δ' ε : Proof V} → δ ↠ δ' → appP δ ε ↠ appP δ' ε
↠-appP = respects-RT (λ _ _ → appPl) _ _

↠-imp*l : ∀ {V} {P P' Q : Path V} → P ↠ P' → P ⊃* Q ↠ P' ⊃* Q
↠-imp*l = respects-RT (λ _ _ → imp*l) _ _

↠-imp*r : ∀ {V} {P Q Q' : Path V} → Q ↠ Q' → P ⊃* Q ↠ P ⊃* Q'
↠-imp*r = respects-RT (λ _ _ → imp*r) _ _

↠-imp* : ∀ {V} {P P' Q Q' : Path V} → P ↠ P' → Q ↠ Q' → P ⊃* Q ↠ P' ⊃* Q'
↠-imp* P↠P' Q↠Q' = trans (↠-imp*l P↠P') (↠-imp*r Q↠Q')
--TODO Duplication

↠-app*l : ∀ {V} {M N : Term V} {P P' Q} → P ↠ P' → app* M N P Q ↠ app* M N P' Q
↠-app*l = respects-RT (λ _ _ → app*l) _ _

↠-app*ref : ∀ {V} {M M' N N' : Term V} {P} → N ↠ N' → app* M M' (reff N) P ↠ app* M M' (reff N') P
↠-app*ref = respects-RT (λ _ _ → reffR) _ _

↠-dir : ∀ {V d} {P Q : Path V} → P ↠ Q → dir d P ↠ dir d Q
↠-dir = respects-RT (λ _ _ → dirR) _ _

↠-APPP : ∀ {V} {δ δ' : Proof V} εε → δ ↠ δ' → APPP δ εε ↠ APPP δ' εε
↠-APPP εε = respects-RT (λ _ _ → ⇒-APPP εε) _ _

record Reduces-to-Λ {V} (M : Term V) : Set where
  constructor reduces-to-Λ 
  field
    A : Type
    N : Term (V , -Term)
    red : M ↠ ΛT A N

-- If Mx1...xn ->> N with n >= 1 then either N = M'x1...xn where M ->> M', or M reduces to a lambda-term
APPl-red : ∀ {V M N M' N'} (NN : snocList (Term V)) →
  M ↠ N → M ≡ APPl (appT M' N') NN → Σ[ M'' ∈ Term V ] (M' ↠ M'' × N ≡ APPl (appT M'' N') NN) ⊎ Reduces-to-Λ M'
APPl-red NN (inc M⇒N) M≡M'NN with APPl-⇒ NN M⇒N M≡M'NN
APPl-red _ (inc M⇒N) M≡M'NN | inj₁ (M'' ,p M'⇒M'' ,p N≡M''NN) = inj₁ (M'' ,p inc M'⇒M'' ,p N≡M''NN)
APPl-red {M' = M'} _ (inc M⇒N) M≡M'NN | inj₂ (A ,p M'' ,p M'≡ΛM'') = inj₂ (reduces-to-Λ A M'' (subst (λ x → M' ↠ x) M'≡ΛM'' ref))
APPl-red _ ref M≡M'NN = inj₁ (_ ,p ref ,p M≡M'NN)
APPl-red NN (trans M↠N N↠P) M≡M'NN with APPl-red NN M↠N M≡M'NN
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₁ (N' ,p M'↠N' ,p N≡N'NN) with APPl-red NN N↠P N≡N'NN
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₁ (N' ,p M'↠N' ,p N≡N'NN) | inj₁ (P' ,p N'↠P' ,p P≡P'NN) = inj₁ (P' ,p trans M'↠N' N'↠P' ,p P≡P'NN)
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₁ (N' ,p M'↠N' ,p N≡N'NN) | inj₂ (reduces-to-Λ _ _ N'↠ΛN₀) = inj₂ (reduces-to-Λ _ _ (trans M'↠N' N'↠ΛN₀))
APPl-red NN (trans M↠N N↠P) M≡M'NN | inj₂ N'rtΛ = inj₂ N'rtΛ

imp-red-inj₁' : ∀ {V} {φ ψ χ χ' : Term V} → χ ↠ χ' → χ ≡ φ ⊃ ψ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
                      (χ' ≡ φ' ⊃ ψ' × φ ↠ φ')
imp-red-inj₁' {χ' = χ'} (inc χ⇒χ') χ≡φ⊃ψ with imp-osr-inj₁ (subst (λ x → x ⇒ χ') χ≡φ⊃ψ χ⇒χ')
imp-red-inj₁' (inc χ⇒χ') χ≡φ⊃ψ | φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p φ⇒?φ' = φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p sub-R-RT φ⇒?φ'
imp-red-inj₁' {φ = φ} {ψ} ref χ≡φ⊃ψ = φ ,p ψ ,p χ≡φ⊃ψ ,p ref
imp-red-inj₁' (trans χ₁↠χ₂ χ₂↠χ₃) χ₁≡φ⊃ψ with imp-red-inj₁' χ₁↠χ₂ χ₁≡φ⊃ψ
imp-red-inj₁' (trans χ₁↠χ₂ χ₂↠χ₃) χ₁≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' with imp-red-inj₁' χ₂↠χ₃ χ₂≡φ'⊃ψ'
imp-red-inj₁' (trans χ₁↠χ₂ χ₂↠χ₃) χ₁≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' | φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p φ'↠φ'' = φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p trans φ↠φ' φ'↠φ''

imp-red-inj₁ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → φ ↠ φ'
imp-red-inj₁ φ⊃ψ↠φ'⊃ψ' with imp-red-inj₁' φ⊃ψ↠φ'⊃ψ' refl
imp-red-inj₁ {φ = φ} φ⊃ψ↠φ'⊃ψ' | φ'' ,p ψ'' ,p φ'⊃ψ'≡φ''⊃ψ'' ,p φ↠φ'' = subst (λ x → φ ↠ x) (⊃-injl (≡-sym φ'⊃ψ'≡φ''⊃ψ'')) φ↠φ''

imp-red-inj₂' : ∀ {V} {φ ψ χ χ' : Term V} → χ ↠ χ' → χ ≡ φ ⊃ ψ → Σ[ φ' ∈ Term V ] Σ[ ψ' ∈ Term V ]
                      (χ' ≡ φ' ⊃ ψ' × ψ ↠ ψ')
imp-red-inj₂' {χ' = χ'} (inc χ⇒χ') χ≡φ⊃ψ with imp-osr-inj₂ (subst (λ x → x ⇒ χ') χ≡φ⊃ψ χ⇒χ')
imp-red-inj₂' (inc χ⇒χ') χ≡φ⊃ψ | φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p φ⇒?φ' = φ' ,p ψ' ,p χ'≡φ'⊃ψ' ,p sub-R-RT φ⇒?φ'
imp-red-inj₂' {φ = φ} {ψ} ref χ≡φ⊃ψ = φ ,p ψ ,p χ≡φ⊃ψ ,p ref
imp-red-inj₂' (trans χ₂↠χ₂ χ₂↠χ₃) χ₂≡φ⊃ψ with imp-red-inj₂' χ₂↠χ₂ χ₂≡φ⊃ψ
imp-red-inj₂' (trans χ₂↠χ₂ χ₂↠χ₃) χ₂≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' with imp-red-inj₂' χ₂↠χ₃ χ₂≡φ'⊃ψ'
imp-red-inj₂' (trans χ₂↠χ₂ χ₂↠χ₃) χ₂≡φ⊃ψ | φ' ,p ψ' ,p χ₂≡φ'⊃ψ' ,p φ↠φ' | φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p φ'↠φ'' = φ'' ,p ψ'' ,p χ₃≡φ''⊃ψ'' ,p trans φ↠φ' φ'↠φ''

imp-red-inj₂ : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ↠ φ' ⊃ ψ' → ψ ↠ ψ'
imp-red-inj₂ φ⊃ψ↠φ'⊃ψ' with imp-red-inj₂' φ⊃ψ↠φ'⊃ψ' refl
imp-red-inj₂ {ψ = ψ} φ⊃ψ↠φ'⊃ψ' | φ'' ,p ψ'' ,p φ'⊃ψ'≡φ''⊃ψ'' ,p ψ↠ψ'' = subst (λ x → ψ ↠ x) (⊃-injr (≡-sym φ'⊃ψ'≡φ''⊃ψ'')) ψ↠ψ''

red-appPl : ∀ {V} {δ ε δ₁ δ₂ : Proof V} → δ ↠ ε → δ ≡ appP δ₁ δ₂ → Σ[ δ₁' ∈ Proof V ] (δ₁ ↠ δ₁' × ε ≡ appP δ₁' δ₂) ⊎ Σ[ φ ∈ Term V ] Σ[ δ' ∈ Proof (V , -Proof) ] δ₁ ↠ ΛP φ δ'
red-appPl (inc (βP {φ = φ} {δ})) Λφδε≡δ₁δ₂ = inj₂ (_ ,p (_ ,p subst (λ x → x ↠ ΛP φ δ) (appP-injl Λφδε≡δ₁δ₂) ref))
red-appPl (inc (appPl {δ' = δ'} δ⇒δ')) δ≡δ₁δ₂ = inj₁ (δ' ,p inc (subst (λ x → x ⇒ δ') (appP-injl δ≡δ₁δ₂) δ⇒δ') ,p cong (appP δ') (appP-injr δ≡δ₁δ₂))
red-appPl (inc refdir) ()
red-appPl (inc univplus) ()
red-appPl (inc univminus) ()
red-appPl (inc (dirR _)) ()
red-appPl {δ₁ = δ₁} ref δ≡δ₁δ₂ = inj₁ (δ₁ ,p (ref ,p δ≡δ₁δ₂))
red-appPl (trans δ↠ε ε↠ε') δ≡δ₁δ₂ with red-appPl δ↠ε δ≡δ₁δ₂
red-appPl (trans δ↠ε ε↠ε') δ≡δ₁δ₂ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) with red-appPl ε↠ε' ε≡δ₁'δ₂
red-appPl (trans δ↠ε ε↠ε') δ≡δ₁δ₂ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) | inj₁ (δ₁'' ,p δ₁'↠δ₁'' ,p ε'≡δ₁''δ₂) = inj₁ (δ₁'' ,p trans δ₁↠δ₁' δ₁'↠δ₁'' ,p ε'≡δ₁''δ₂)
red-appPl (trans δ↠ε ε↠ε') δ≡δ₁δ₂ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) | inj₂ (φ ,p δ₁'' ,p δ₁'↠Λδ₁'') = inj₂ (φ ,p (δ₁'' ,p (trans δ₁↠δ₁' δ₁'↠Λδ₁'')))
red-appPl (trans δ↠ε δ↠ε₁) δ≡δ₁δ₂ | inj₂ δ₁↠Λ = inj₂ δ₁↠Λ

bot-red-bot : ∀ {V} {φ ψ : Term V} → φ ↠ ψ → φ ≡ ⊥ → ψ ≡ ⊥
bot-red-bot (inc βT) ()
bot-red-bot (inc (appTl _)) ()
bot-red-bot (inc (impl _)) ()
bot-red-bot (inc (impr _)) ()
bot-red-bot ref φ≡⊥ = φ≡⊥
bot-red-bot (trans φ₁↠φ₂ φ₂↠φ₃) φ₁≡⊥ = bot-red-bot φ₂↠φ₃ (bot-red-bot φ₁↠φ₂ φ₁≡⊥)

bot-not-red-imp : ∀ {V} {φ ψ : Term V} → ⊥ ↠ φ ⊃ ψ → Empty
bot-not-red-imp {V} {φ} {ψ} ⊥↠φ⊃ψ with bot-red-bot ⊥↠φ⊃ψ refl
bot-not-red-imp ⊥↠φ⊃ψ | ()

λλλ-red-ref : ∀ {V A} {P P' : Path V} {Q} → P ↠ P' → P ≡ λλλ A Q → P' ≡ λλλ A Q
λλλ-red-ref (inc βE) ()
λλλ-red-ref (inc βPP) ()
λλλ-red-ref (inc ref⊃*) ()
λλλ-red-ref (inc ref⊃*univ) ()
λλλ-red-ref (inc univ⊃*ref) ()
λλλ-red-ref (inc univ⊃*univ) ()
λλλ-red-ref (inc (imp*l _)) ()
λλλ-red-ref (inc (imp*r _)) ()
λλλ-red-ref (inc (app*l _)) ()
λλλ-red-ref (inc (reffR _)) ()

λλλ-red-ref ref P≡λQ = P≡λQ
λλλ-red-ref (trans P↠P' P'↠P'') P≡λQ = λλλ-red-ref P'↠P'' (λλλ-red-ref P↠P' P≡λQ)
