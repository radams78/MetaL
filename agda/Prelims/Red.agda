--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.Red
--------------------------------------------------------------
-- Reduction Relations
--------------------------------------------------------------

module Prelims.Red where
open import Relation.Binary
open import Prelims.Closure
open import Prelims.Closure.RST

-- Define the proposition: "x and y have a common reduct w.r.t. R and S"
record Common-Reduct {i} {A : Set} (R S : Rel A i) (x y : A) : Set i where
  constructor cr
  field
    reduct : A
    left   : R x reduct
    right  : S y reduct

--Common reduct is symmetric
cr-sym : ∀ {i A R S x y} → Common-Reduct {i} {A} R S x y → Common-Reduct S R y x
cr-sym (cr z xRz ySz) = cr z ySz xRz

-- R and S satisfy the diamond property iff, whenever xRy and xSz, then y and z have a common reduct
-- wrt S and R
Diamond : ∀ {i} {A} → Rel A i → Rel A i → Set i
Diamond R S = ∀ x y z → R x y → S x z → Common-Reduct S R y z

-- Let ->> be the reflexive transitive closure of R, and ~= its reflexive symmetric transitive closure
-- Then R satisfies Church-Rosser iff, whenever x ~= y, then x and y have a common reduct wrt ->>
Church-Rosser : ∀ {i A} → Rel A i → Set i
Church-Rosser R = ∀ x y → RSTClose R x y → Common-Reduct (RTClose R) (RTClose R) x y

-- If R is confluent then R satisfies Church-Rosser
diamondRT-CR : ∀ {i A} {R : Rel A i} →
  Diamond (RTClose R) (RTClose R) → Church-Rosser R
diamondRT-CR diamond x y (inc xRy) = cr y (inc xRy) ref
diamondRT-CR diamond x .x ref = cr x ref ref
diamondRT-CR diamond y x (sym x≃y) = cr-sym (diamondRT-CR diamond x y x≃y)
diamondRT-CR diamond x z (trans x≃y y≃z) = 
  let cr a x↠a y↠a = diamondRT-CR diamond x _ x≃y in 
  let cr b y↠b z↠b = diamondRT-CR diamond _ z y≃z in 
  let cr c a↠c b↠c = diamond _ a b y↠a y↠b in 
  cr c (trans x↠a a↠c) (trans z↠b b↠c)