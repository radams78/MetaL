open import Grammar.Base

module Grammar.OpFamily.OpFamily (G : Grammar) where

open import Prelims
open Grammar G
open import Grammar.OpFamily.LiftFamily G
open import Grammar.OpFamily.Composition G 

record OpFamily : Set₂ where
  field
    liftFamily : LiftFamily
    comp : Composition liftFamily liftFamily liftFamily
  open LiftFamily liftFamily public
  open Composition comp public

  assoc : ∀ {U} {V} {W} {X} 
    {τ : Op W X} {σ : Op V W} {ρ : Op U V} → 
    τ ∘ (σ ∘ ρ) ∼op (τ ∘ σ) ∘ ρ
  assoc {U} {V} {W} {X} {τ} {σ} {ρ} {K} x = let open ≡-Reasoning in 
    begin 
      apV (τ ∘ (σ ∘ ρ)) x
    ≡⟨ apV-comp ⟩
      ap τ (apV (σ ∘ ρ) x)
    ≡⟨ cong (ap τ) apV-comp ⟩
      ap τ (ap σ (apV ρ x))
    ≡⟨⟨ ap-comp (apV ρ x) ⟩⟩
      ap (τ ∘ σ) (apV ρ x)
    ≡⟨⟨ apV-comp ⟩⟩
      apV ((τ ∘ σ) ∘ ρ) x
    ∎

  unitl : ∀ {U} {V} {σ : Op U V} → idOp V ∘ σ ∼op σ
  unitl {U} {V} {σ} {K} x = let open ≡-Reasoning in 
    begin 
      apV (idOp V ∘ σ) x
    ≡⟨ apV-comp ⟩
      ap (idOp V) (apV σ x)
    ≡⟨ ap-idOp ⟩
      apV σ x
    ∎

  unitr : ∀ {U} {V} {σ : Op U V} → σ ∘ idOp U ∼op σ
  unitr {U} {V} {σ} {K} x = let open ≡-Reasoning in
    begin 
      apV (σ ∘ idOp U) x
    ≡⟨ apV-comp ⟩
      ap σ (apV (idOp U) x)
    ≡⟨ cong (ap σ) (apV-idOp x) ⟩
      apV σ x
    ∎

  ups : ∀ {V} {KK} → Op V (snoc-extend V KK)
  ups {V} {[]} = idOp V
  ups {KK = KK snoc _} = up ∘ ups {KK = KK}

  liftOp-up : ∀ {U} {V} {C} {K} {L}
    {σ : Op U V} (E : Subexp U C K) →
    ap (liftOp L σ) (ap up E) ≡ ap up (ap σ E)
  liftOp-up E = liftOp-up-mixed comp comp refl {E = E}

