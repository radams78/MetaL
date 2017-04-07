module PHOML.PathSub.RefSub where
open import Relation.Binary.PropositionalEquality
open import PHOML.Grammar
open import PHOML.PathSub.Base
open import PHOML.PathSub.PR
open import PHOML.PathSub.RP
open import PHOML.PathSub.SP
open import PHOML.PathSub.BotPathSub

refSub : ∀ {V} → PathSub V V
refSub x = reff (var x)

botPathSub-upRep : ∀ {V} {P : Path V} → (x₀::= P •PR upRep) ∼∼ refSub
botPathSub-upRep x₀ = refl
botPathSub-upRep (↑ x) = refl

botSub₃-liftRefSub : ∀ {V} {M N : Term V} {P : Path V} →
  (x₂:= M ,x₁:= N ,x₀:= P) •SP liftPathSub refSub ∼∼ x₀::= P
botSub₃-liftRefSub x₀ = refl
botSub₃-liftRefSub (↑ x) = refl

liftsRep-liftRefSub : ∀ {U V} {ρ : Rep U V} → (liftsRep pathDom ρ •RP liftPathSub refSub) ∼∼ (liftPathSub refSub •PR liftRep -Term ρ)
liftsRep-liftRefSub x₀ = refl
liftsRep-liftRefSub (↑ x) = refl
