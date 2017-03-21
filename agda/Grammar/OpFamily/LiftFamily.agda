open import Grammar.Base

module Grammar.OpFamily.LiftFamily (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily.PreOpFamily G
open import Grammar.OpFamily.Lifting G

record IsLiftFamily (F : PreOpFamily) (L : Lifting F) : Set₁ where
  open PreOpFamily F
  open Lifting L
  field
    liftOp-x₀ : ∀ {U} {V} {K} {σ : Op U V} → 
      apV (liftOp K σ) x₀ ≡ var x₀
    liftOp-↑ : ∀ {U} {V} {K} {L} {σ : Op U V} (x : Var U L) →
      apV (liftOp K σ) (↑ x) ≡ ap up (apV σ x)

  liftOp-idOp : ∀ {V} {K} → liftOp K (idOp V) ∼op idOp (V , K)
  liftOp-idOp {V} {K} x₀ = let open ≡-Reasoning in
    begin
      apV (liftOp K (idOp V)) x₀
    ≡⟨ liftOp-x₀ ⟩
      var x₀
    ≡⟨⟨ apV-idOp x₀ ⟩⟩
      apV (idOp (V , K)) x₀
    ∎
  liftOp-idOp {V} {K} {L} (↑ x) = let open ≡-Reasoning in 
    begin 
      apV (liftOp K (idOp V)) (↑ x)
    ≡⟨ liftOp-↑ x ⟩
      ap up (apV (idOp V) x)
    ≡⟨ cong (ap up) (apV-idOp x) ⟩
      ap up (var x)              
    ≡⟨ apV-up ⟩
      var (↑ x)
    ≡⟨⟨ apV-idOp (↑ x) ⟩⟩
      apV (idOp (V , K)) (↑ x)
    ∎

  liftsOp-idOp : ∀ {V} A → 
    liftsOp A (idOp V) ∼op idOp (extend V A)
  liftsOp-idOp [] = ∼-refl
  liftsOp-idOp {V} (K ∷ A) = let open EqReasoning (OP (extend V (K ∷ A)) (extend V (K ∷ A))) in
    begin
      liftsOp A (liftOp K (idOp V))
    ≈⟨ liftsOp-cong A liftOp-idOp ⟩
      liftsOp A (idOp (V , K))
    ≈⟨ liftsOp-idOp A ⟩
      idOp (extend V (K ∷ A))
    ∎

  ap-idOp : ∀ {V} {C} {K} {E : Subexp V C K} → ap (idOp V) E ≡ E
  ap-idOp {E = var x} = apV-idOp x
  ap-idOp {E = app c EE} = cong (app c) ap-idOp
  ap-idOp {E = []} = refl
  ap-idOp {V} {E = _∷_ {A = SK A _} E F} =
    let open ≡-Reasoning in 
    begin
      ap (liftsOp A (idOp V)) E ∷ ap (idOp V) F
    ≡⟨ cong₂ _∷_ (ap-congl (liftsOp-idOp A) E) ap-idOp ⟩
       ap (idOp (extend V A)) E ∷ F
    ≡⟨ cong (λ x → x ∷ F) ap-idOp ⟩
       E ∷ F
    ∎

record LiftFamily : Set₂ where
  field
    preOpFamily : PreOpFamily
    lifting : Lifting preOpFamily
    isLiftFamily : IsLiftFamily preOpFamily lifting
  open PreOpFamily preOpFamily public
  open Lifting lifting public
  open IsLiftFamily isLiftFamily public
