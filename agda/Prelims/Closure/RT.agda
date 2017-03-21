--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.Closure.Refl
--------------------------------------------------------------
-- Reflexive transitive closure of a relation
--------------------------------------------------------------

module Prelims.Closure.RT where
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (trans)
import Relation.Binary.PropositionalEquality.Core
open import Prelims.Closure.Refl
open import Prelims.Respect

-- The reflexive transitive closure of a relation
data RTClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → RTClose R x y
  ref : ∀ {x} → RTClose R x x
  trans : ∀ {x} {y} {z} → RTClose R x y → RTClose R y z → RTClose R x z

-- The closure is a preorder
RTCLOSE : ∀ {i A} → Rel A i → Preorder _ _ _
RTCLOSE {i} {A} R = record { 
  Carrier = A ; 
  _≈_ = _≡_ ; 
  _∼_ = RTClose R ; 
  isPreorder = record { 
    isEquivalence = Relation.Binary.PropositionalEquality.Core.isEquivalence ; 
    reflexive = λ { {x} .{x} refl → ref } ; 
    trans = trans } }

-- If R ⊆ S then closure of R ⊆ closure of S
monoRT : ∀ {i A} {R S : Rel A i} {x y} → (∀ {x y} → R x y → S x y) → RTClose R x y → RTClose S x y
monoRT R⊆S (inc Rxy) = inc (R⊆S Rxy)
monoRT R⊆S ref = ref
monoRT R⊆S (trans RTxy RTyz) = trans (monoRT R⊆S RTxy) (monoRT R⊆S RTyz)

-- Reflexive closure ⊆ reflexive transitive closure
sub-R-RT : ∀ {i} {A} {R : Rel A i} {x} {y} → RClose {A = A} R x y → RTClose R x y
sub-R-RT (inc xRy) = inc xRy
sub-R-RT ref = ref

-- If f respects R and S then it respects closure of R and closure of S
respects-RT : ∀ {i j A B} {R : Rel A i} {S : Rel B j} {f : A → B} →
  Respects₂ f R S → Respects₂ f (RTClose R) (RTClose S)
respects-RT hyp x y (inc x⇒y) = inc (hyp x y x⇒y)
respects-RT _ _ _ ref = ref
respects-RT hyp x z (trans x↠y y↠z) = trans (respects-RT hyp x _ x↠y) (respects-RT hyp _ z y↠z)

