module PHOML.Meta.PathSub where
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Rules
open import PHOML.Meta.Sub
open import PHOML.Meta.ConVal

_∶_≡_∶_⟶_ : ∀ {U V} → PathSub U V → Sub U V → Sub U V → Context V → Context U → Set
τ ∶ ρ ≡ σ ∶ Γ ⟶ Δ = ∀ x → Γ ⊢ τ x ∶ ρ _ x ≡〈 typeof' x Δ 〉 σ _ x

botPathSub-typed : ∀ {V} {Γ : Context V} {A} {P : Path V} {M N} →
  Γ ⊢ P ∶ M ≡〈 A 〉 N → x₀::= P ∶ x₀:= M ≡ x₀:= N ∶ Γ ⟶ Γ ,T A
botPathSub-typed {Γ = Γ} {A} {P} {M} {N} Γ⊢P∶M≡N x₀ = Γ⊢P∶M≡N
botPathSub-typed {Γ = Γ} Γ⊢P∶M≡N (↑ x) = refR (change-type (varR x (context-validity Γ⊢P∶M≡N)) (≡-sym (≡-trans (cong ty (yt-rep (typeof x Γ))) ty-yt)))

liftPathSub-typed : ∀ {U V} {τ : PathSub U V} {ρ σ Γ Δ A} →
  τ ∶ ρ ≡ σ ∶ Γ ⟶ Δ → valid Γ → liftPathSub τ ∶ sub↖ ρ ≡ sub↗ σ ∶ addpath Γ A ⟶ Δ ,T A
liftPathSub-typed τ∶ρ≡σ validΓ x₀ = varR x₀ (valid-addpath validΓ)
liftPathSub-typed {τ = τ} {ρ} {σ} {Γ = Γ} {Δ} {A = A} τ∶ρ≡σ validΓ (↑ x) = subst₄ (λ x₃ y z w → addpath Γ A ⊢ x₃ ∶ y ≡〈 z 〉 w) 
  (rep-•R₃ (τ x)) (rep-•R₃ (ρ -Term x)) (≡-sym (yt-rep (typeof x Δ))) (rep-•R₃ (σ -Term x)) 
  (weakening (τ∶ρ≡σ x) (valid-addpath validΓ) (upRep₃-addpath-typed A))

path-substitution : ∀ {U} {V} {Γ : Context U} {Δ : Context V} 
  {ρ} {σ} {τ} {M} {A} →
  Γ ⊢ M ∶ A → τ ∶ ρ ≡ σ ∶ Δ ⟶ Γ →
  ρ ∶ Δ ⟶ Γ → σ ∶ Δ ⟶ Γ → 
  valid Δ → 
  Δ ⊢ M ⟦⟦ τ ∶ ρ ≡ σ ⟧⟧ ∶ M ⟦ ρ ⟧ ≡〈 yt A 〉 M ⟦ σ ⟧
path-substitution (varR x _) τ∶ρ≡σ _ _ _ = τ∶ρ≡σ x
path-substitution (appTR {A = A} Γ⊢M∶A⇛B Γ⊢N∶A) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = 
  appER (substitution Γ⊢N∶A validΔ ρ∶Δ⟶Γ) (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ) (path-substitution Γ⊢M∶A⇛B τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ) 
    (path-substitution Γ⊢N∶A τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ)
path-substitution {Δ = Δ} {ρ} {σ} (ΛTR {A = A} {M = M} Γ,A⊢M∶B) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = lllR (ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed ρ∶Δ⟶Γ (ctxTR validΔ)))) 
  (ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)))) 
  (convER (path-substitution Γ,A⊢M∶B (liftPathSub-typed τ∶ρ≡σ validΔ) (sub↖-typed ρ∶Δ⟶Γ validΔ) (sub↗-typed σ∶Δ⟶Γ validΔ) (valid-addpath validΔ)) 
  (appTR (ΛTR (weakening (weakening (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) 
                                               (liftSub-typed ρ∶Δ⟶Γ (ctxTR validΔ))) 
                                    (ctxTR (ctxTR validΔ))
                                    (liftRep-typed (upRep-typed (ty A)))) 
                         (ctxTR (ctxTR (ctxTR validΔ))) 
                         (liftRep-typed (upRep-typed (ty A)))) 
              (ctxTR (valid-addpath validΔ)) 
              (liftRep-typed (upRep-typed (var x₁ ≡〈 A 〉 var x₀))))) 
         (varR x₂ (valid-addpath validΔ))) 
  (appTR (ΛTR (weakening (weakening (weakening (substitution Γ,A⊢M∶B (ctxTR validΔ) 
                                               (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ))) 
                                    (ctxTR (ctxTR validΔ))
                                    (liftRep-typed (upRep-typed (ty A)))) 
                         (ctxTR (ctxTR (ctxTR validΔ))) 
                         (liftRep-typed (upRep-typed (ty A)))) 
              (ctxTR (valid-addpath validΔ)) 
              (liftRep-typed (upRep-typed (var x₁ ≡〈 A 〉 var x₀))))) 
         (varR x₁ (valid-addpath validΔ))) 
  (sym (inc (subst
               (λ x → appT (ΛT A (M ⟦ liftSub -Term ρ ⟧) ⇑ ⇑ ⇑) (var x₂) ⇒ x) 
            (≡-sym (sub↖-decomp {E = M})) βT))) 
  (sym (inc (subst
               (λ x → appT (ΛT A (M ⟦ liftSub -Term σ ⟧) ⇑ ⇑ ⇑) (var x₁) ⇒ x) 
            (≡-sym (sub↗-decomp {E = M})) βT))))
path-substitution (⊥R _) _ _ _ validΔ = refR (⊥R validΔ)
path-substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ = ⊃*R 
  (path-substitution Γ⊢φ∶Ω τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ) 
  (path-substitution Γ⊢ψ∶Ω τ∶ρ≡σ ρ∶Δ⟶Γ σ∶Δ⟶Γ validΔ)

