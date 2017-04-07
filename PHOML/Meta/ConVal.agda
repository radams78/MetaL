module PHOML.Meta.ConVal where
open import Prelims
open import PHOML.Grammar
open import PHOML.Red
open import PHOML.Rules

valid-addpath : ∀ {V} {Γ : Context V} {A} → valid Γ → valid (addpath Γ A)
valid-addpath validΓ = ctxER (varR x₁ (ctxTR (ctxTR validΓ))) (varR x₀ (ctxTR (ctxTR validΓ)))

context-validity' : ∀ {V} {Γ : Context V} {A} → valid (addpath Γ A) → valid Γ
context-validity' (ctxER (varR _ (ctxTR (ctxTR validΓ))) _) = validΓ

context-validity : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} →
                   Γ ⊢ M ∶ A → valid Γ
context-validity (varR _ validΓ) = validΓ
context-validity (appTR Γ⊢M∶A⇛B _) = context-validity Γ⊢M∶A⇛B
context-validity (ΛTR Γ,A⊢M∶B) with context-validity Γ,A⊢M∶B
context-validity (ΛTR _) | ctxTR validΓ = validΓ
context-validity (⊥R validΓ) = validΓ
context-validity (⊃R Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (appPR Γ⊢δ∶φ⊃ψ _) = context-validity Γ⊢δ∶φ⊃ψ
context-validity (ΛPR Γ⊢φ∶Ω _ _) = context-validity Γ⊢φ∶Ω
context-validity (convPR Γ⊢M∶A _ _) = context-validity Γ⊢M∶A
context-validity (refR Γ⊢M∶A) = context-validity Γ⊢M∶A
context-validity (⊃*R Γ⊢φ∶Ω _) = context-validity Γ⊢φ∶Ω
context-validity (univR Γ⊢δ∶φ⊃ψ _) = context-validity Γ⊢δ∶φ⊃ψ
context-validity (plusR Γ⊢P∶φ≡ψ) = context-validity Γ⊢P∶φ≡ψ
context-validity (minusR Γ⊢P∶φ≡ψ) = context-validity Γ⊢P∶φ≡ψ
context-validity (lllR Γ⊢M∶A _ _) = context-validity Γ⊢M∶A
context-validity (appER Γ⊢N∶A _ _ _) = context-validity Γ⊢N∶A
context-validity (convER Γ⊢P∶M≡N _ _ _ _) = context-validity Γ⊢P∶M≡N

context-validityP : ∀ {V} {Γ : Context V} {φ} → valid (Γ ,P φ) → Γ ⊢ φ ∶ ty Ω
context-validityP (ctxPR Γ⊢φ∶Ω) = Γ⊢φ∶Ω

weakening : ∀ {U} {V} {ρ : Rep U V} {K}
           {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
           Γ ⊢ M ∶ A → valid Δ → ρ ∶ Γ ⇒R Δ → Δ ⊢ M 〈 ρ 〉 ∶ A 〈 ρ 〉
weakening {ρ = ρ} (varR x _) validΔ ρ∶Γ⇒RΔ = change-type (varR (ρ _ x) validΔ) (ρ∶Γ⇒RΔ x)
weakening (appTR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ ρ∶Γ⇒RΔ = appTR (weakening Γ⊢M∶A⇛B validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N∶A validΔ ρ∶Γ⇒RΔ)
weakening (ΛTR Γ,A⊢M∶B) validΔ ρ∶Γ⇒RΔ = ΛTR (weakening Γ,A⊢M∶B (ctxTR validΔ) (liftRep-typed ρ∶Γ⇒RΔ))
weakening (⊥R _) validΔ _ = ⊥R validΔ
weakening (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ ρ∶Γ⇒RΔ = ⊃R (weakening Γ⊢φ∶Ω validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ψ∶Ω validΔ ρ∶Γ⇒RΔ)
weakening (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ ρ∶Γ⇒RΔ = appPR (weakening Γ⊢δ∶φ⊃ψ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ε∶φ validΔ ρ∶Γ⇒RΔ)
weakening {ρ = ρ} {Δ = Δ} (ΛPR {φ = φ} {ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ψ) validΔ ρ∶Γ⇒RΔ = 
  let Δ⊢φ∶Ω : Δ ⊢ φ 〈 ρ 〉 ∶ ty Ω
      Δ⊢φ∶Ω = weakening Γ⊢φ∶Ω validΔ ρ∶Γ⇒RΔ in
  ΛPR Δ⊢φ∶Ω
      (weakening Γ⊢ψ∶Ω validΔ ρ∶Γ⇒RΔ) 
      (change-type (weakening Γ,φ⊢δ∶ψ (ctxPR Δ⊢φ∶Ω) (liftRep-typed ρ∶Γ⇒RΔ)) (liftRep-upRep ψ))
weakening {ρ = ρ} (convPR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ ρ∶Γ⇒RΔ = convPR (weakening Γ⊢δ∶φ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ψ∶Ω validΔ ρ∶Γ⇒RΔ) (≃-resp-rep φ≃ψ)
weakening (refR Γ⊢M∶A) validΔ ρ∶Γ⇒RΔ = refR (weakening Γ⊢M∶A validΔ ρ∶Γ⇒RΔ)
weakening (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ ρ∶Γ⇒RΔ = ⊃*R (weakening Γ⊢P∶φ≡φ' validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢Q∶ψ≡ψ' validΔ ρ∶Γ⇒RΔ)
weakening (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ ρ∶Γ⇒RΔ = univR (weakening Γ⊢δ∶φ⊃ψ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢ε∶ψ⊃φ validΔ ρ∶Γ⇒RΔ)
weakening (plusR Γ⊢P∶φ≡ψ) validΔ ρ∶Γ⇒RΔ = plusR (weakening Γ⊢P∶φ≡ψ validΔ ρ∶Γ⇒RΔ)
weakening (minusR Γ⊢P∶φ≡ψ) validΔ ρ∶Γ⇒RΔ = minusR (weakening Γ⊢P∶φ≡ψ validΔ ρ∶Γ⇒RΔ)
weakening (lllR {B = B} {M = M} {N} Γ⊢M∶A Γ⊢N∶A ΓAAE⊢P∶Mx≡Ny) validΔ ρ∶Γ⇒RΔ = lllR 
  (weakening Γ⊢M∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N∶A validΔ ρ∶Γ⇒RΔ) 
  (change-type (weakening ΓAAE⊢P∶Mx≡Ny (valid-addpath validΔ) (liftRep-typed (liftRep-typed (liftRep-typed ρ∶Γ⇒RΔ)))) 
  (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) (liftRep-upRep₃ M) (liftRep-upRep₃ N)))
weakening (appER Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ ρ∶Γ⇒RΔ = appER (weakening Γ⊢N∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N'∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢P∶M≡M' validΔ ρ∶Γ⇒RΔ) 
  (weakening Γ⊢Q∶N≡N' validΔ ρ∶Γ⇒RΔ)
weakening (convER Γ⊢M∶N₁≡N₂ Γ⊢N₁'∶A Γ⊢N₂'∶A N₁≃N₁' N₂≃N₂') validΔ ρ∶Γ⇒RΔ =
  convER (weakening Γ⊢M∶N₁≡N₂ validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N₁'∶A validΔ ρ∶Γ⇒RΔ) (weakening Γ⊢N₂'∶A validΔ ρ∶Γ⇒RΔ) (≃-resp-rep N₁≃N₁') (≃-resp-rep N₂≃N₂')

context-validity-Prop : ∀ {V} {Γ : Context V} {p : Var V -Proof} →
  valid Γ → Γ ⊢ typeof p Γ ∶ ty Ω
context-validity-Prop {p = ()} 〈〉R
context-validity-Prop {p = ↑ p} (ctxTR {A = A} validΓ) = weakening (context-validity-Prop validΓ) (ctxTR validΓ) (upRep-typed (ty A))
context-validity-Prop {p = x₀} (ctxPR {φ = φ} Γ⊢φ∶Ω) = weakening Γ⊢φ∶Ω (ctxPR Γ⊢φ∶Ω) (upRep-typed φ)
context-validity-Prop {p = ↑ p} (ctxPR {φ = φ} Γ⊢φ∶Ω) = weakening (context-validity-Prop (context-validity Γ⊢φ∶Ω)) (ctxPR Γ⊢φ∶Ω) (upRep-typed φ)
context-validity-Prop {p = ↑ p} (ctxER {M = M} {N} {A} Γ⊢M∶A Γ⊢N∶A) = weakening (context-validity-Prop (context-validity Γ⊢M∶A)) (ctxER Γ⊢M∶A Γ⊢N∶A) (upRep-typed (M ≡〈 A 〉 N))
--TODO Refactor - general ctx rule

context-validity-Eq₁ : ∀ {V} {Γ : Context V} {e : Var V -Path} → valid Γ → Γ ⊢ left (typeof e Γ) ∶ ty (type (typeof e Γ))
context-validity-Eq₁ {e = ()} 〈〉R
context-validity-Eq₁ {e = ↑ e} (ctxTR {Γ = Γ} {A = A} validΓ) = subst₂ (λ x y → Γ ,T A ⊢ x ∶ y) (left-rep (typeof e Γ)) (cong ty (≡-sym (type-rep (typeof e Γ)))) (weakening (context-validity-Eq₁ {e = e} validΓ) (ctxTR validΓ) (upRep-typed (ty A)))
context-validity-Eq₁ {e = ↑ e} (ctxPR {Γ = Γ} {φ = φ} Γ⊢φ∶Ω) = subst₂ (λ x y → Γ ,P φ ⊢ x ∶ y) (left-rep (typeof e Γ)) (cong ty (≡-sym (type-rep (typeof e Γ)))) (weakening (context-validity-Eq₁ {e = e} (context-validity Γ⊢φ∶Ω)) (ctxPR Γ⊢φ∶Ω) (upRep-typed φ))
context-validity-Eq₁ {e = x₀} (ctxER {Γ = Γ} {M} {N} {A} Γ⊢M∶A Γ⊢N∶A) = weakening Γ⊢M∶A (ctxER Γ⊢M∶A Γ⊢N∶A) (upRep-typed (M ≡〈 A 〉 N))
context-validity-Eq₁ {e = ↑ e} (ctxER {Γ = Γ} {M} {N} {A} Γ⊢M∶A Γ⊢N∶A) = subst₂ (λ x y → Γ ,E M ≡〈 A 〉 N ⊢ x ∶ y) (left-rep (typeof e Γ)) (cong ty (≡-sym (type-rep (typeof e Γ)))) (weakening (context-validity-Eq₁ {e = e} (context-validity Γ⊢M∶A)) (ctxER Γ⊢M∶A Γ⊢N∶A) (upRep-typed (M ≡〈 A 〉 N)))
--TODO Duplication

context-validity-Eq₂ : ∀ {V} {Γ} {e : Var V -Path} → valid Γ → Γ ⊢ right (typeof e Γ) ∶ ty (type (typeof e Γ))
context-validity-Eq₂ {e = ()} 〈〉R
context-validity-Eq₂ {e = ↑ e} (ctxTR {Γ = Γ} {A = A} validΓ) = subst₂ (λ x y → Γ ,T A ⊢ x ∶ y) (right-rep (typeof e Γ)) (cong ty (≡-sym (type-rep (typeof e Γ)))) (weakening (context-validity-Eq₂ {e = e} validΓ) (ctxTR validΓ) (upRep-typed (ty A)))
context-validity-Eq₂ {e = ↑ e} (ctxPR {Γ = Γ} {φ = φ} Γ⊢φ∶Ω) = subst₂ (λ x y → Γ ,P φ ⊢ x ∶ y) (right-rep (typeof e Γ)) (cong ty (≡-sym (type-rep (typeof e Γ)))) (weakening (context-validity-Eq₂ {e = e} (context-validity Γ⊢φ∶Ω)) (ctxPR Γ⊢φ∶Ω) (upRep-typed φ))
context-validity-Eq₂ {e = x₀} (ctxER {Γ = Γ} {M} {N} {A} Γ⊢M∶A Γ⊢N∶A) = weakening Γ⊢N∶A (ctxER Γ⊢M∶A Γ⊢N∶A) (upRep-typed (M ≡〈 A 〉 N))
context-validity-Eq₂ {e = ↑ e} (ctxER {Γ = Γ} {M} {N} {A} Γ⊢M∶A Γ⊢N∶A) = subst₂ (λ x y → Γ ,E M ≡〈 A 〉 N ⊢ x ∶ y) (right-rep (typeof e Γ)) (cong ty (≡-sym (type-rep (typeof e Γ)))) (weakening (context-validity-Eq₂ {e = e} (context-validity Γ⊢M∶A)) (ctxER Γ⊢M∶A Γ⊢N∶A) (upRep-typed (M ≡〈 A 〉 N)))

weaken-prop : ∀ {V K} {Γ : Context V} {φ} {E : VExpression V K} {T} → Γ ⊢ E ∶ T → Γ ⊢ φ ∶ ty Ω → Γ ,P φ ⊢ E ⇑ ∶ T ⇑
weaken-prop {φ = φ} Γ⊢E∶T Γ⊢φ∶Ω = weakening Γ⊢E∶T (ctxPR Γ⊢φ∶Ω) (upRep-typed φ)

weaken-prop₂ : ∀ {V K} {Γ : Context V} {φ ψ} {E : VExpression V K} {T} → 
  Γ ⊢ E ∶ T → Γ ⊢ φ ∶ ty Ω → Γ ⊢ ψ ∶ ty Ω → Γ ,P φ ,P ψ ⇑ ⊢ E ⇑ ⇑ ∶ T ⇑ ⇑
weaken-prop₂ Γ⊢E∶T Γ⊢φ∶Ω Γ⊢ψ∶Ω = weaken-prop (weaken-prop Γ⊢E∶T Γ⊢φ∶Ω) (weaken-prop Γ⊢ψ∶Ω Γ⊢φ∶Ω)

{- app*R' : ∀ {V} {Γ : Context V} {P Q : Path V} {M M' N N' : Term V} {A B : Type} →
                   Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' → Γ ⊢ Q ∶ N ≡〈 A 〉 N' →
                   -------------------------------------------------
                   Γ ⊢ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'
app*R' Γ⊢P∶M≡M' Γ⊢Q∶N≡N' = appER (eq-validity₁ Γ⊢Q∶N≡N' refl) (eq-validity₂ Γ⊢Q∶N≡N' refl) Γ⊢P∶M≡M' Γ⊢Q∶N≡N' -}
