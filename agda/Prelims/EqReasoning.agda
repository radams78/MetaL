--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.EqReasoning
--------------------------------------------------------------
-- Reasoning with equations and inequalities
--------------------------------------------------------------

module Prelims.EqReasoning where
open import Relation.Binary public hiding (_⇒_)
import Relation.Binary.PreorderReasoning
import Relation.Binary.EqReasoning
open import Relation.Binary.PropositionalEquality public using (_≡_;refl;cong;cong₂;subst;subst₂;setoid) renaming (sym to ≡-sym;trans to ≡-trans)

-- To the PreorderReasoning module in the standard library,
-- we add a rule: given a proof of x ≡ y, we can use the step y ∼ x

module PreorderReasoning {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where
  open Relation.Binary.PreorderReasoning P public

  infixr 2 _≈⟨⟨_⟩⟩_
  _≈⟨⟨_⟩⟩_ : ∀ x {y z} → Preorder._≈_ P y x → y IsRelatedTo z → x IsRelatedTo z
  x ≈⟨⟨ y≈x ⟩⟩ y∼z = x ≈⟨ Preorder.Eq.sym P y≈x ⟩ y∼z

-- To the EqReasoning module in the standard library,
-- we add two rules:
-- given a proof of x ≡ y, we can use the step y ≈ x
-- given a proof of x ≈ y, we can use the step y ≈ x

module EqReasoning {s₁ s₂} (S : Setoid s₁ s₂) where
  open Setoid S using (_≈_)
  open Relation.Binary.EqReasoning S public
  open Relation.Binary.PropositionalEquality public

  infixr 2 _≡⟨⟨_⟩⟩_
  _≡⟨⟨_⟩⟩_ : ∀ x {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
  x ≡⟨⟨ y≡x ⟩⟩ y≈z = x ≡⟨ sym y≡x ⟩ y≈z

  infixr 2 _≈⟨⟨_⟩⟩_
  _≈⟨⟨_⟩⟩_ : ∀ x {y z} → y ≈ x → y IsRelatedTo z → x IsRelatedTo z
  x ≈⟨⟨ y≈x ⟩⟩ y≈z = x ≈⟨ Setoid.sym S  y≈x ⟩ y≈z

-- To the PreorderReasoning module in the standard library,
-- we add a rule: given a proof of x ≡ y, we can use the step y ≡ x
module ≡-Reasoning where
-- We use Relation.Binary.EqReasoning instead of Relation.Binary.PropositionalEquality for backwards comapatibility with older versions of the standard library

  module _ {a} {A : Set a} where
    open Relation.Binary.EqReasoning (setoid A) public
  
    infixr 2 _≡⟨⟨_⟩⟩_
    _≡⟨⟨_⟩⟩_ : ∀ (x : A) {y z} → y ≡ x → y IsRelatedTo z → x IsRelatedTo z
    _ ≡⟨⟨ y≡x ⟩⟩ (Relation.Binary.PreorderReasoning.relTo y≡z) = Relation.Binary.PreorderReasoning.relTo (Setoid.trans (setoid A) (≡-sym y≡x) y≡z)

-- Congruence results for three and four equations at a time

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'} →
          a ≡ a' → b ≡ b' → c ≡ c' → f a b c ≡ f a' b' c'
cong₃ _ refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a' b b' c c' d d'} →
          a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → f a b c d ≡ f a' b' c' d'
cong₄ _ refl refl refl refl = refl

subst₃ : ∀ {A B C : Set} (P : A → B → C → Set) {a a' b b' c c'} →
           a ≡ a' → b ≡ b' → c ≡ c' → P a b c → P a' b' c'
subst₃ _ refl refl refl Pabc = Pabc

subst₄ : ∀ {A1 A2 A3 A4 : Set} (P : A1 → A2 -> A3 -> A4  → Set) 
             {a1 a1' a2 a2' a3 a3' a4 a4'} →
           a1 ≡ a1' -> a2 ≡ a2' -> a3 ≡ a3' -> a4 ≡ a4' ->
           P a1 a2 a3 a4 -> P a1' a2' a3' a4'
subst₄ _ refl refl refl refl Paaaa = Paaaa
