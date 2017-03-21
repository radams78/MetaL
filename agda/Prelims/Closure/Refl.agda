--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.Closure.Refl
--------------------------------------------------------------
-- Reflexive closure of a relation
--------------------------------------------------------------

module Prelims.Closure.Refl where
open import Relation.Binary
open import Prelims.Respect

-- The reflexive closure of a relation
data RClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x} {y} → R x y → RClose R x y
  ref : ∀ {x} → RClose R x x

-- A function that respects R and S will respect theri reflexive closures
respects-R₂ : ∀ {i j} {A B : Set} {f : A → B} {R : Rel A i} {S : Rel B j} →
  Respects₂ f R S → Respects₂ f (RClose R) (RClose S)
respects-R₂ hyp x y (inc x⇒y) = inc (hyp x y x⇒y)
respects-R₂ _ _ _ ref = ref

respects-R : ∀ {i A} (f : A → A) (R : Rel A i) → Respects f R → Respects f (RClose R)
respects-R _ _ = respects-R₂

