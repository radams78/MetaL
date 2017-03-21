open import Grammar.Base

module Grammar.OpFamily.PreOpFamily (G : Grammar) where
open import Prelims.EqReasoning
open Grammar G

record PreOpFamily : Set₂ where
  field
    Op : Alphabet → Alphabet → Set
    apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
    up : ∀ {V} {K} → Op V (V , K)
    apV-up : ∀ {V} {K} {L} {x : Var V K} → apV (up {K = L}) x ≡ var (↑ x)
    idOp : ∀ V → Op V V
    apV-idOp : ∀ {V} {K} (x : Var V K) → apV (idOp V) x ≡ var x

  _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
  _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x
    
  ∼-refl : ∀ {U} {V} {σ : Op U V} → σ ∼op σ
  ∼-refl _ = refl
    
  ∼-sym : ∀ {U} {V} {σ τ : Op U V} → σ ∼op τ → τ ∼op σ
  ∼-sym σ-is-τ x = ≡-sym (σ-is-τ x)

  ∼-trans : ∀ {U} {V} {ρ σ τ : Op U V} → ρ ∼op σ → σ ∼op τ → ρ ∼op τ
  ∼-trans ρ-is-σ σ-is-τ x = ≡-trans (ρ-is-σ x) (σ-is-τ x)

  OP : Alphabet → Alphabet → Setoid _ _
  OP U V = record { 
     Carrier = Op U V ; 
     _≈_ = _∼op_ ; 
     isEquivalence = record { 
       refl = ∼-refl ; 
       sym = ∼-sym ; 
       trans = ∼-trans } }
