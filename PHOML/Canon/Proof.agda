module PHOML.Canon.Proof where
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,p_)
open import Data.Sum
open import Prelims
open import PHOML.Grammar
open import PHOML.Neutral
open import PHOML.Red

data CanonP (V : Alphabet) : Set where
  neutral : NeutralP V → CanonP V
  Λ : Term V → Proof (V , -Proof) → CanonP V

decode-CanonP : ∀ {V} → CanonP V → Proof V
decode-CanonP (neutral δ) = decode-NeutralP δ
decode-CanonP (Λ φ δ) = ΛP φ δ

--TODO Make imp and ⊃ consistent throughout
reflect-CanonP : ∀ {U V} {δ : Proof U} {ρ : Rep U V} {χ : CanonP V} → δ 〈 ρ 〉 ≡ decode-CanonP χ → Σ[ χ' ∈ CanonP U ] δ ≡ decode-CanonP χ'
reflect-CanonP {δ = δ} {ρ} {χ = neutral χ} δρ≡χ = let χ' ,p δ≡χ' = reflect-NeutralP δ χ δρ≡χ in (neutral χ') ,p δ≡χ'
reflect-CanonP {δ = var x} {χ = Λ φ χ} ()
reflect-CanonP {δ = app -lamProof (φ ∷ (δ ∷ []))} δρ≡χ = (Λ φ δ) ,p refl
reflect-CanonP {δ = app -appProof x₁} {χ = Λ φ χ} ()
reflect-CanonP {δ = app (-dir x) x₁} {χ = Λ φ χ} ()
--TODO Common pattern in reflect lemmas

app-canonl' : ∀ {V} {δ ε : Proof V} {χ : CanonP V} → appP δ ε ≡ decode-CanonP χ → Σ[ χ' ∈ CanonP V ] δ ≡ decode-CanonP χ'
app-canonl' {χ = neutral (var _)} ()
app-canonl' {χ = neutral (app δ _)} δε≡δε = neutral δ ,p appP-injl δε≡δε
app-canonl' {χ = neutral (dirN _ _)} ()
app-canonl' {χ = Λ _ _} ()

pre-app-wnl' : ∀ {V} {δ ε χ : Proof V} {χ' : CanonP V} → appP δ ε ⇒ χ → χ ≡ decode-CanonP χ' → Σ[ χ'' ∈ CanonP V ] δ ↠ decode-CanonP χ''
pre-app-wnl' βP _ = (Λ _ _) ,p ref
pre-app-wnl' {χ' = neutral (var _)} (appPl _) ()
pre-app-wnl' {δ = δ} {χ' = neutral (app χ'' _)} (appPl δ⇒δ') χ≡χ' = neutral χ'' ,p inc (subst (λ x → δ ⇒ x) (appP-injl χ≡χ') δ⇒δ')
pre-app-wnl' {χ' = neutral (dirN _ _)} (appPl _) ()
pre-app-wnl' {χ' = Λ φ δ} (appPl _) ()

app-wnl' : ∀ {V} {δ ε δ₁ δ₂ : Proof V} {χ : CanonP V} → δ ↠ ε → δ ≡ appP δ₁ δ₂ → ε ≡ decode-CanonP χ → Σ[ χ' ∈ CanonP V ] δ₁ ↠ decode-CanonP χ'
app-wnl' δ↠ε δ≡δ₁δ₂ ε≡χ with red-appPl δ↠ε δ≡δ₁δ₂
app-wnl' {δ₂ = δ₂} {χ} δ↠ε δ≡δ₁δ₂ ε≡χ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) with app-canonl' {δ = δ₁'} {δ₂} {χ} (≡-trans (≡-sym ε≡δ₁'δ₂) ε≡χ)
app-wnl' {δ₁ = δ₁} δ↠ε δ≡δ₁δ₂ ε≡χ | inj₁ (δ₁' ,p δ₁↠δ₁' ,p ε≡δ₁'δ₂) | χ' ,p δ₁'≡χ' = χ' ,p (subst (λ x → δ₁ ↠ x) δ₁'≡χ' δ₁↠δ₁')
app-wnl' δ↠ε δ≡δ₁δ₂ ε≡χ | inj₂ (φ ,p δ₁' ,p δ₁↠Λφδ₁') = Λ φ δ₁' ,p δ₁↠Λφδ₁'

