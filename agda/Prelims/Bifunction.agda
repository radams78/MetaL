--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims.Bifunction
--------------------------------------------------------------
-- Setoid functions with two arguments
--------------------------------------------------------------

open import Relation.Binary public

module Prelims.Bifunction
  {r₁ r₂ s₁ s₂ t₁ t₂} {A : Setoid r₁ r₂} {B : Setoid s₁ s₂} {C : Setoid t₁ t₂} 
  (f : Setoid.Carrier A → Setoid.Carrier B → Setoid.Carrier C) where

-- A function is well-defined in an argument iff
-- it respects equality in that argument

  wdl : Set _
  wdl = ∀ {a a'} → Setoid._≈_ A a a' → ∀ b → Setoid._≈_ C (f a b) (f a' b)

  wdr : Set _
  wdr = ∀ a {b b'} → Setoid._≈_ B b b' → Setoid._≈_ C (f a b) (f a b')

  wd2 : Set _
  wd2 = ∀ {a a' b b'} → Setoid._≈_ A a a' → Setoid._≈_ B b b' → Setoid._≈_ C (f a b) (f a' b')

-- A function is well-defined in both arguments iff
-- it is well-defined in each argument separately

  congl : wd2 → wdl
  congl wd a≈a' _ = wd a≈a' (Setoid.refl B)

  congr : wd2 → wdr
  congr wd _ b≈b' = wd (Setoid.refl A) b≈b'

  cong2 : wdl → wdr → wd2
  cong2 wdl wdr {_} {a'} {b} a≈a' b≈b' = Setoid.trans C (wdl a≈a' b) (wdr a' b≈b')

