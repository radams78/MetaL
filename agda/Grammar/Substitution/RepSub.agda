open import Grammar.Base

module Grammar.Substitution.RepSub (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G

open OpFamily REP using () renaming (liftsOp to liftsOpR)
open PreOpFamily pre-substitution
open Lifting LIFTSUB

rep2sub : ∀ {U} {V} → Rep U V → Sub U V
rep2sub ρ K x = var (ρ K x)

liftRep-is-liftSub : ∀ {U} {V} {ρ : Rep U V} {K} → 
  rep2sub (liftRep K ρ) ∼ liftSub K (rep2sub ρ)
liftRep-is-liftSub x₀ = refl
liftRep-is-liftSub (↑ _) = refl

up-is-up : ∀ {V} {K} → rep2sub (upRep {V} {K}) ∼ upSub
up-is-up _ = refl

liftsOp-is-liftsOp : ∀ {U} {V} {ρ : Rep U V} {A} → 
  rep2sub (liftsOpR  A ρ) ∼ liftsOp A (rep2sub ρ)
liftsOp-is-liftsOp {ρ = ρ} {A = []} = ∼-refl {σ = rep2sub ρ}
liftsOp-is-liftsOp {U} {V} {ρ} {K ∷ A} = let open EqReasoning (OP _ _) in 
  begin
    rep2sub (liftsOpR A (liftRep K ρ))
  ≈⟨ liftsOp-is-liftsOp {A = A} ⟩
    liftsOp A (rep2sub (liftRep K ρ))
  ≈⟨ liftsOp-cong A liftRep-is-liftSub ⟩
    liftsOp A (liftSub K (rep2sub ρ))
  ∎

rep-is-sub : ∀ {U} {V} {K} {C} (E : Subexp U K C) {ρ : Rep U V} → 
  E 〈 ρ 〉 ≡ E ⟦ rep2sub ρ ⟧
rep-is-sub (var _) = refl
rep-is-sub (app c E) = cong (app c) (rep-is-sub E)
rep-is-sub [] = refl
rep-is-sub {U} {V} (_∷_ {A = SK AA _} E F) {ρ} = cong₂ _∷_ 
  (let open ≡-Reasoning in
  begin 
    E 〈 liftsOpR AA ρ 〉
  ≡⟨ rep-is-sub E ⟩
    E ⟦ (λ K x → var (liftsOpR AA ρ K x)) ⟧ 
  ≡⟨ ap-congl (liftsOp-is-liftsOp {A = AA}) E ⟩
    E ⟦ liftsOp AA (λ K x → var (ρ K x)) ⟧
  ∎)
  (rep-is-sub F)

up-is-up' : ∀ {V} {C} {K} {L} {E : Subexp V C K} → 
  E 〈 upRep {K = L} 〉 ≡ E ⟦ upSub ⟧
up-is-up' {E = E} = rep-is-sub E
