module PHOML.PathSub.ExtendPS where
open import Relation.Binary.PropositionalEquality
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.SP

extendPS : ∀ {U} {V} → PathSub U V → Path V → PathSub (U , -Term) V
extendPS τ P x₀ = P
extendPS τ P (↑ x) = τ x

botSub₃-liftPathSub : ∀ {U V} {M N : Term V} {P} {τ : PathSub U V} →
  ((x₂:= M ,x₁:= N ,x₀:= P) •SP liftPathSub τ) ∼∼ extendPS τ P
botSub₃-liftPathSub x₀ = refl
botSub₃-liftPathSub (↑ x) = botSub-upRep₃
