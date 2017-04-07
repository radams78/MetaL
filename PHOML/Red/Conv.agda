module PHOML.Red.Conv where
open import Data.Unit
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure.RST public
open import PHOML.Grammar
open import PHOML.Red.Base
open import PHOML.Red.RTRed
open import PHOML.Red.Diamond

_≃_ : ∀ {V K} → Expression V K → Expression V K → Set
_≃_ {V} {K} = RSTClose (_⇒_ {V} {K})

≃-resp-rep : ∀ {U V K} {E F : Expression U K} {ρ : Rep U V} → E ≃ F → E 〈 ρ 〉 ≃ F 〈 ρ 〉
≃-resp-rep {ρ = ρ} = respects-RST (λ _ _ → ⇒-resp-rep) _ _

≃-resp-sub : ∀ {U V} {M N : Term U} {σ : Sub U V} → M ≃ N → M ⟦ σ ⟧ ≃ N ⟦ σ ⟧
≃-resp-sub = respects-RST (λ _ _ → ⇒-resp-sub) _ _

≃-impl : ∀ {V} {φ φ' ψ : Term V} → φ ≃ φ' → φ ⊃ ψ ≃ φ' ⊃ ψ
≃-impl {V} = respects-RST (λ _ _ → impl) _ _

≃-impr : ∀ {V} {φ ψ ψ' : Term V} → ψ ≃ ψ' → φ ⊃ ψ ≃ φ ⊃ ψ'
≃-impr {V} = respects-RST (λ _ _ → impr) _ _

≃-imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ≃ φ' → ψ ≃ ψ' → φ ⊃ ψ ≃ φ' ⊃ ψ'
≃-imp φ≃φ' ψ≃ψ' = trans (≃-impl φ≃φ') (≃-impr ψ≃ψ')

≃-appTl : ∀ {V} {M M' N : Term V} → M ≃ M' → appT M N ≃ appT M' N
≃-appTl {V} = respects-RST (λ _ _ → appTl) _ _

PHOML-Church-Rosser : ∀ {V K} {E F : VExpression V K} → E ≃ F → Common-Reduct _↠_ _↠_ E F
PHOML-Church-Rosser (inc E⇒F) = cr _ (inc E⇒F) ref
PHOML-Church-Rosser ref = cr _ ref ref
PHOML-Church-Rosser (sym E≃F) = 
  let cr G E↠G F↠G = PHOML-Church-Rosser E≃F in cr G F↠G E↠G
PHOML-Church-Rosser (trans E≃F F≃G) = 
  let cr H E↠H F↠H = PHOML-Church-Rosser E≃F in 
  let cr K F↠K G↠K = PHOML-Church-Rosser F≃G in 
  let cr L H↠L K↠L = diamond F↠H F↠K in 
  cr L (trans E↠H H↠L) (trans G↠K K↠L)

≃-⊃-injl : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≃ φ' ⊃ ψ' → φ ≃ φ'
≃-⊃-injl {V} {φ} {φ'} {ψ} {ψ'} φ⊃ψ≃φ'⊃ψ' = 
  let cr χ φ⊃ψ↠χ φ'⊃ψ'↠χ = PHOML-Church-Rosser φ⊃ψ≃φ'⊃ψ' in 
  let φ₀ ,p ψ₀ ,p χ≡φ₀⊃ψ₀ ,p φ↠φ₀ = imp-red-inj₁' φ⊃ψ↠χ refl in
  trans (sub-RT-RST φ↠φ₀) (sym (sub-RT-RST (imp-red-inj₁ (subst (λ x → φ' ⊃ ψ' ↠ x) χ≡φ₀⊃ψ₀ φ'⊃ψ'↠χ))))

≃-⊃-injr : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ⊃ ψ ≃ φ' ⊃ ψ' → ψ ≃ ψ'
≃-⊃-injr {V} {φ} {φ'} {ψ} {ψ'} φ⊃ψ≃φ'⊃ψ' = 
  let cr χ φ⊃ψ↠χ φ'⊃ψ'↠χ = PHOML-Church-Rosser φ⊃ψ≃φ'⊃ψ' in 
  let φ₀ ,p ψ₀ ,p χ≡φ₀⊃ψ₀ ,p ψ↠ψ₀ = imp-red-inj₂' φ⊃ψ↠χ refl in
  trans (sub-RT-RST ψ↠ψ₀) (sym (sub-RT-RST (imp-red-inj₂ (subst (λ x → φ' ⊃ ψ' ↠ x) χ≡φ₀⊃ψ₀ φ'⊃ψ'↠χ))))

≃-yt : ∀ {V A B} → A ≃ B → yt {V} A ≡ yt B
≃-yt (inc ())
≃-yt ref = refl
≃-yt (sym A≃B) = ≡-sym (≃-yt A≃B)
≃-yt (trans A≃B B≃C) = ≡-trans (≃-yt A≃B) (≃-yt B≃C)

≃-ty-inj : ∀ {V A B} → ty {V} A ≃ ty B → A ≡ B
≃-ty-inj = ≃-yt

