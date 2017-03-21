--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.Respect
--------------------------------------------------------------
-- Functions respecting relations
--------------------------------------------------------------

module Prelims.Respect where
open import Level
open import Relation.Binary

-- A function f respects relations R and S iff, whenever x R y, then f(x) S f(y)

Respects₂ : ∀ {i j k l} {A : Set i} {B : Set j} (f : A → B) (R : Rel A k) (S : Rel B l) → Set (i ⊔ k ⊔ l)
Respects₂ f R S = ∀ x y → R x y → S (f x) (f y)

-- A function f respects a relation R iff, whenever x R y, then f(x) R f(y)

Respects : ∀ {i j} {A : Set i} → (A → A) → Rel A j → Set (i ⊔ j)
Respects f R = Respects₂ f R R
