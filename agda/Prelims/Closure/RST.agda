--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.Closure.RST
--------------------------------------------------------------
-- Reflexive symmetric transitive closure of a relation
--------------------------------------------------------------

module Prelims.Closure.RST where
open import Relation.Binary
open import Prelims.Closure.RT
open import Prelims.Respect

-- The reflexive symmetric transitive closure of a relation
data RSTClose {i} {A : Set} (R : Rel A i) : Rel A i where
  inc : ∀ {x y} → R x y → RSTClose R x y
  ref : ∀ {x} → RSTClose R x x
  sym : ∀ {x y} → RSTClose R x y → RSTClose R y x
  trans : ∀ {x y z} → RSTClose R x y → RSTClose R y z → RSTClose R x z

-- The closure is a setoid
RSTCLOSE : ∀ {i A} → Rel A i → Setoid _ _
RSTCLOSE {i} {A} R = record { 
  Carrier = A ; 
  _≈_ = RSTClose R ; 
  isEquivalence = record { 
    refl = ref ; 
    sym = sym ; 
    trans = trans } }

-- Reflexive transitive closure ⊆ RST closure
sub-RT-RST : ∀ {i A} {R : Rel A i} {x y} → RTClose {A = A} R x y → RSTClose R x y
sub-RT-RST (inc xRy) = inc xRy
sub-RT-RST ref = ref
sub-RT-RST (trans xRTy yRTz) = trans (sub-RT-RST xRTy) (sub-RT-RST yRTz)

-- If f respects R and S then f respects closure of R and closure of S
respects-RST : ∀ {i j A B} {f : A → B} {R : Rel A i} {S : Rel B j} →
  Respects₂ f R S → Respects₂ f (RSTClose R) (RSTClose S)
respects-RST hyp x y (inc x⇒y) = inc (hyp x y x⇒y)
respects-RST hyp y .y ref = ref
respects-RST hyp x y (sym y≃x) = sym (respects-RST hyp y x y≃x)
respects-RST hyp x z (trans x≃y y≃z) = trans (respects-RST hyp x _ x≃y) (respects-RST hyp _ z y≃z)
