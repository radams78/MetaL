open import Grammar.Base
open import Data.List
open import Prelims
open import Function.Equality hiding (cong;_∘_)

module Grammar.OpFamily.Composition (A : Grammar) where
open Grammar A hiding (_⟶_)
open import Grammar.OpFamily.LiftFamily A
open LiftFamily

record Composition (F G H : LiftFamily) : Set where
  infix 25 _∘_
  field
    _∘_ : ∀ {U} {V} {W} → Op F V W → Op G U V → Op H U W
    liftOp-comp' : ∀ {U V W K σ ρ} → 
      _∼op_ H (liftOp H K (_∘_ {U} {V} {W} σ ρ)) 
        (liftOp F K σ ∘ liftOp G K ρ)
    apV-comp : ∀ {U} {V} {W} {K} {σ} {ρ} {x : Var U K} → 
      apV H (_∘_ {U} {V} {W} σ ρ) x ≡ ap F σ (apV G ρ x)

  comp-cong : ∀ {U V W} {σ σ' : Op F V W} {ρ ρ' : Op G U V} → 
    _∼op_ F σ σ' → _∼op_ G ρ ρ' → _∼op_ H (σ ∘ ρ) (σ' ∘ ρ')
  comp-cong {U} {V} {W} {σ} {σ'} {ρ} {ρ'} σ∼σ' ρ∼ρ' x = let open ≡-Reasoning in 
    begin
      apV H (σ ∘ ρ) x
    ≡⟨ apV-comp ⟩
      ap F σ (apV G ρ x)
    ≡⟨ ap-cong F σ∼σ' (ρ∼ρ' x) ⟩
      ap F σ' (apV G ρ' x)
    ≡⟨⟨ apV-comp ⟩⟩
      apV H (σ' ∘ ρ') x
    ∎

  comp-congl : ∀ {U} {V} {W} {σ σ' : Op F V W} →
    _∼op_ F σ σ' → ∀ (ρ : Op G U V) → _∼op_ H (σ ∘ ρ) (σ' ∘ ρ)
  comp-congl {U} {V} {W} = congl {A = OP F V W} {B = OP G U V} {C = OP H U W} _∘_ comp-cong

  comp-congr : ∀ {U} {V} {W} (σ : Op F V W) {ρ ρ' : Op G U V} →
    _∼op_ G ρ ρ' → _∼op_ H (σ ∘ ρ) (σ ∘ ρ')
  comp-congr {U} {V} {W} = congr {A = OP F V W} {B = OP G U V} {C = OP H U W} _∘_ comp-cong

  liftsOp-comp : ∀ {U V W} A {σ ρ} → 
    _∼op_ H (liftsOp H A (_∘_ {U} {V} {W} σ ρ)) 
      (liftsOp F A σ ∘ liftsOp G A ρ)
  liftsOp-comp [] = ∼-refl H
  liftsOp-comp {U} {V} {W} (K ∷ A) {σ} {ρ} = let open EqReasoning (OP H _ _) in 
    begin
      liftsOp H A (liftOp H K (σ ∘ ρ))
    ≈⟨ liftsOp-cong H A liftOp-comp' ⟩
      liftsOp H A (liftOp F K σ ∘ liftOp G K ρ)
    ≈⟨ liftsOp-comp A ⟩
      liftsOp F A (liftOp F K σ) ∘ liftsOp G A (liftOp G K ρ)
    ∎

  ap-comp : ∀ {U V W C K} (E : Subexp U C K) {σ ρ} → 
    ap H (_∘_ {U} {V} {W} σ ρ) E ≡ ap F σ (ap G ρ E)
  ap-comp (var _) = apV-comp
  ap-comp (app c E) = cong (app c) (ap-comp E)
  ap-comp [] = refl
  ap-comp (_∷_ {A = SK A _} E E') {σ} {ρ} = cong₂ _∷_
    (let open ≡-Reasoning in 
    begin
      ap H (liftsOp H A (σ ∘ ρ)) E
    ≡⟨ ap-congl H (liftsOp-comp A) E ⟩
      ap H (liftsOp F A σ ∘ liftsOp G A ρ) E
    ≡⟨ ap-comp E ⟩
      ap F (liftsOp F A σ) (ap G (liftsOp G A ρ) E)
    ∎) 
    (ap-comp E')

  liftOp-comp : ∀ {U V W K C L ρ σ} {M : Subexp (U , K) C L} →
    ap H (liftOp H K (_∘_ {U} {V} {W} σ ρ)) M ≡ ap F (liftOp F K σ) (ap G (liftOp G K ρ) M)
  liftOp-comp {U} {V} {W} {K} {C} {L} {ρ} {σ} {M} = let open ≡-Reasoning in 
    begin 
      ap H (liftOp H K (σ ∘ ρ)) M
    ≡⟨ ap-congl H liftOp-comp' M ⟩
      ap H (liftOp F K σ ∘ liftOp G K ρ) M
    ≡⟨ ap-comp M ⟩
      ap F (liftOp F K σ) (ap G (liftOp G K ρ) M)
    ∎

ap-comp-sim : ∀ {F F' G G' H} (comp₁ : Composition F G H) (comp₂ : Composition F' G' H) {U} {V} {V'} {W}
  {σ : Op F V W} {ρ : Op G U V} {σ' : Op F' V' W} {ρ' : Op G' U V'} →
  _∼op_ H (Composition._∘_ comp₁ σ ρ) (Composition._∘_ comp₂ σ' ρ') →
  ∀ {C} {K} (E : Subexp U C K) →
  ap F σ (ap G ρ E) ≡ ap F' σ' (ap G' ρ' E)
ap-comp-sim {F} {F'} {G} {G'} {H} comp₁ comp₂ {U} {V} {V'} {W} {σ} {ρ} {σ'} {ρ'} hyp {C} {K} E =
  let open ≡-Reasoning in 
  begin
    ap F σ (ap G ρ E)
  ≡⟨⟨ Composition.ap-comp comp₁ E {σ} {ρ} ⟩⟩
    ap H (Composition._∘_ comp₁ σ ρ) E
  ≡⟨ ap-congl H hyp E ⟩
    ap H (Composition._∘_ comp₂ σ' ρ') E
  ≡⟨ Composition.ap-comp comp₂ E {σ'} {ρ'} ⟩
    ap F' σ' (ap G' ρ' E)
  ∎

liftOp-up-mixed : ∀ {F} {G} {H} {F'} (comp₁ : Composition F G H) (comp₂ : Composition F' F H)
  {U} {V} {C} {K} {L} {σ : Op F U V} →
  (∀ {V} {C} {K} {L} {E : Subexp V C K} → ap F (up F {V} {L}) E ≡ ap F' (up F' {V} {L}) E) →
  ∀ {E : Subexp U C K} → ap F (liftOp F L σ) (ap G (up G) E) ≡ ap F' (up F') (ap F σ E)
liftOp-up-mixed {F} {G} {H} {F'} comp₁ comp₂ {U} {V} {C} {K} {L} {σ} hyp {E = E} = ap-comp-sim comp₁ comp₂ 
  (λ x → let open ≡-Reasoning in 
  begin
    apV H (Composition._∘_ comp₁ (liftOp F L σ) (up G)) x
  ≡⟨ Composition.apV-comp comp₁ ⟩
    ap F (liftOp F L σ) (apV G (up G) x)
  ≡⟨ cong (ap F (liftOp F L σ)) (apV-up G) ⟩
    apV F (liftOp F L σ) (↑ x)
  ≡⟨ liftOp-↑ F x ⟩
    ap F (up F) (apV F σ x)
  ≡⟨ hyp {E = apV F σ x}⟩
    ap F' (up F') (apV F σ x)
  ≡⟨⟨ Composition.apV-comp comp₂ ⟩⟩
    apV H (Composition._∘_ comp₂ (up F') σ) x
  ∎) 
  E
