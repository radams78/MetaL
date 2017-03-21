--------------------------------------------------------------
-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Prelims
--------------------------------------------------------------
-- Lists which cons on the right ('snoc')
--------------------------------------------------------------

module Prelims.Snoclist where
open import Relation.Binary.PropositionalEquality

infixl 20 _snoc_
data snocList (A : Set) : Set where
  [] : snocList A
  _snoc_ : snocList A → A → snocList A

snocmap : ∀ {A B} → (A → B) → snocList A → snocList B
snocmap f [] = []
snocmap f (aa snoc a) = snocmap f aa snoc f a

snocmap-comp : ∀ {A B C} {g : B → C} {f : A → B} (l : snocList A) →
  snocmap (λ x → g (f x)) l ≡ snocmap g (snocmap f l)
snocmap-comp [] = refl
snocmap-comp {g = g} {f = f} (l snoc a) = cong (λ x → x snoc g (f a)) (snocmap-comp l)

data HetsnocList {A} (B : A → Set) : snocList A → Set where
  [] : HetsnocList B []
  _snoc_ : ∀ {aa} {a} → HetsnocList B aa → B a → HetsnocList B (aa snoc a)
