open import Grammar.Base

module Grammar.OpFamily.Lifting (G : Grammar) where
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Prelims
open Grammar G renaming (_⟶_ to _⇒_)
open import Grammar.OpFamily.PreOpFamily G

record Lifting (F : PreOpFamily) : Set₁ where
  open PreOpFamily F
  field
    liftOp : ∀ {U} {V} A → Op U V → Op (U , A) (V , A)
    liftOp-cong : ∀ {V} {W} {A} {ρ σ : Op V W} → ρ ∼op σ → liftOp A ρ ∼op liftOp A σ

  liftsOp : ∀ {U} {V} AA → Op U V → Op (extend U AA) (extend V AA)
  liftsOp [] σ = σ
  liftsOp (A ∷ AA) σ = liftsOp AA (liftOp A σ)

  liftsOp-cong : ∀ {U} {V} AA {ρ σ : Op U V} → ρ ∼op σ → liftsOp AA ρ ∼op liftsOp AA σ
  liftsOp-cong [] ρ∼σ = ρ∼σ
  liftsOp-cong (A ∷ AA) ρ∼σ = liftsOp-cong AA (liftOp-cong ρ∼σ)

  ap : ∀ {U} {V} {C} {K} → Op U V → Subexp U C K → Subexp V C K
  ap ρ (var x) = apV ρ x
  ap ρ (app c EE) = app c (ap ρ EE)
  ap _ [] = []
  ap ρ (_∷_ {A = SK AA _} E EE) = ap (liftsOp AA ρ) E ∷ ap ρ EE

  ap-congl : ∀ {U} {V} {C} {K} 
    {ρ σ : Op U V} → ρ ∼op σ → ∀ (E : Subexp U C K) →
    ap ρ E ≡ ap σ E
  ap-congl ρ-is-σ (var x) = ρ-is-σ x
  ap-congl ρ-is-σ (app c E) = cong (app c) (ap-congl ρ-is-σ E)
  ap-congl _ [] = refl
  ap-congl ρ-is-σ (_∷_ {A = SK AA _} E F) = 
    cong₂ _∷_ (ap-congl (liftsOp-cong AA ρ-is-σ) E) (ap-congl ρ-is-σ F)

  ap-congr : ∀ {U} {V} {C} {K} {σ : Op U V} {E F : Subexp U C K} → E ≡ F → ap σ E ≡ ap σ F
  ap-congr {σ = σ} = cong (ap σ)

  ap-cong : ∀ {U} {V} {C} {K}
    {ρ σ : Op U V} {M N : Subexp U C K} →
    ρ ∼op σ → M ≡ N → ap ρ M ≡ ap σ N
  ap-cong {U} {V} {C} {K} =
    cong2 {A = OP U V} {B = setoid (Subexp U C K)} {C = setoid (Subexp V C K)} 
    ap ap-congl (λ _ → ap-congr)
