module PHOML.Meta.Sub where
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.Red.Conv
open import PHOML.Rules
open import PHOML.Meta.ConVal

_∶_⟶_ : ∀ {U V} → Sub U V → Context V → Context U → Set
_∶_⟶_ {U} {V} σ Γ Δ = ∀ {K} (x : Var U K) → Γ ⊢ σ _ x ∶ typeof x Δ ⟦ σ ⟧

botSub-typed : ∀ {V K} {M : VExpression V K} {Γ A} →
  Γ ⊢ M ∶ A → (x₀:= M) ∶ Γ ⟶ (Γ , A)
botSub-typed {V} {K} {M} {Γ} {A} Γ⊢M∶A x₀ = change-type Γ⊢M∶A (≡-sym (botSub-upRep A {M}))
botSub-typed {Γ = Γ} Γ⊢M∶A (↑ x) = change-type (varR x (context-validity Γ⊢M∶A)) (≡-sym (botSub-upRep (typeof x Γ)))

botSub₃-typed : ∀ {V K₂ K₁ K₀} {M₂ : VExpression V K₂} {M₁ : VExpression V K₁} {M₀ : VExpression V K₀} {Γ A₀ A₁ A₂} →
  Γ ⊢ M₂ ∶ A₂ → Γ ⊢ M₁ ∶ A₁ ⟦ x₀:= M₂ ⟧ → Γ ⊢ M₀ ∶ A₀ ⇑ ⟦ x₂:= M₂ ,x₁:= M₁ ,x₀:= M₀ ⟧ → (x₂:= M₂ ,x₁:= M₁ ,x₀:= M₀) ∶ Γ ⟶ (((Γ , A₂) , A₁) , A₀)
botSub₃-typed _ _ Γ⊢M₀∶A₀ x₀ = Γ⊢M₀∶A₀
botSub₃-typed {M₂ = M₂} {M₁} {M₀} {A₁ = A₁} Γ⊢M₂∶A₂ Γ⊢M₁∶A₁ Γ⊢M₀∶A₀ (↑ x₀) = change-type Γ⊢M₁∶A₁ (let open ≡-Reasoning in 
  begin
    A₁ ⟦ x₀:= M₂ ⟧
  ≡⟨⟨ sub-congr A₁ (botSub₃-upRep₂' {M₁ = M₁} {M₀}) ⟩⟩
    A₁ ⟦ (x₂:= M₂ ,x₁:= M₁ ,x₀:= M₀) •SR upRep •SR upRep ⟧
  ≡⟨ sub-•SR A₁ ⟩
    A₁ ⇑ ⟦ (x₂:= M₂ ,x₁:= M₁ ,x₀:= M₀) •SR upRep ⟧
  ≡⟨ sub-•SR (A₁ ⇑) ⟩
    A₁ ⇑ ⇑ ⟦ x₂:= M₂ ,x₁:= M₁ ,x₀:= M₀ ⟧
  ∎)
botSub₃-typed Γ⊢M₂∶A₂ _ _ (↑ (↑ x₀)) = change-type Γ⊢M₂∶A₂ (≡-sym botSub-upRep₃)
botSub₃-typed Γ⊢M₂∶A₂ _ _ (↑ (↑ (↑ x))) = change-type (varR x (context-validity Γ⊢M₂∶A₂)) (≡-sym botSub-upRep₃)

liftSub-typed : ∀ {U V} {σ : Sub U V} {Δ Γ K A} →
  σ ∶ Δ ⟶ Γ → valid (_,_ {V} {K} Δ (A ⟦ σ ⟧)) → liftSub K σ ∶ (Δ , A ⟦ σ ⟧) ⟶ (Γ , A)
liftSub-typed {A = A} σ∶Δ⟶Γ validΔA x₀ = change-type (varR x₀ validΔA) (≡-sym (liftSub-upRep A))
liftSub-typed {σ = σ} {Γ = Γ} {A = A} σ∶Δ⟶Γ validΔA (↑ x) = change-type (weakening (σ∶Δ⟶Γ x) validΔA (upRep-typed (A ⟦ σ ⟧))) (≡-sym (liftSub-upRep (typeof x Γ)))

substitution : ∀ {U} {V} {σ : Sub U V} {K}
  {Γ : Context U} {M : Expression U (varKind K)} {A} {Δ} →
  Γ ⊢ M ∶ A → valid Δ → σ ∶ Δ ⟶ Γ → Δ ⊢ M ⟦ σ ⟧ ∶ A ⟦ σ ⟧
substitution (varR x _) _ σ∶Δ⟶Γ = σ∶Δ⟶Γ x
substitution (appTR Γ⊢M∶A⇛B Γ⊢N∶A) validΔ σ∶Δ⟶Γ = appTR (substitution Γ⊢M∶A⇛B validΔ σ∶Δ⟶Γ) (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ)
substitution (ΛTR Γ,A⊢M∶B) validΔ σ∶Δ⟶Γ = ΛTR (substitution Γ,A⊢M∶B (ctxTR validΔ) (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)))
substitution (⊥R validΓ) validΔ σ∶Δ⟶Γ = ⊥R validΔ
substitution (⊃R Γ⊢φ∶Ω Γ⊢ψ∶Ω) validΔ σ∶Δ⟶Γ = 
  ⊃R (substitution Γ⊢φ∶Ω validΔ σ∶Δ⟶Γ) (substitution Γ⊢ψ∶Ω validΔ σ∶Δ⟶Γ)
substitution (appPR Γ⊢δ∶φ⊃ψ Γ⊢ε∶φ) validΔ σ∶Δ⟶Γ =
  appPR (substitution Γ⊢δ∶φ⊃ψ validΔ σ∶Δ⟶Γ) (substitution Γ⊢ε∶φ validΔ σ∶Δ⟶Γ)
substitution {σ = σ} {Δ = Δ} (ΛPR {φ = φ} {ψ = ψ} Γ⊢φ∶Ω Γ⊢ψ∶Ω Γ,φ⊢δ∶ε) validΔ σ∶Δ⟶Γ = 
  let Δ⊢φ∶Ω : Δ ⊢ φ ⟦ σ ⟧ ∶ ty Ω
      Δ⊢φ∶Ω = substitution Γ⊢φ∶Ω validΔ σ∶Δ⟶Γ in
  let validΔφ : valid (Δ ,P φ ⟦ σ ⟧)
      validΔφ = ctxPR Δ⊢φ∶Ω in
  ΛPR Δ⊢φ∶Ω (substitution Γ⊢ψ∶Ω validΔ σ∶Δ⟶Γ)
  (change-type (substitution Γ,φ⊢δ∶ε validΔφ
    (liftSub-typed σ∶Δ⟶Γ validΔφ)) (liftSub-upRep ψ))
substitution (convPR Γ⊢δ∶φ Γ⊢ψ∶Ω φ≃ψ) validΔ σ∶Δ⟶Γ = 
  convPR (substitution Γ⊢δ∶φ validΔ σ∶Δ⟶Γ) (substitution Γ⊢ψ∶Ω validΔ σ∶Δ⟶Γ) 
  (≃-resp-sub φ≃ψ)
substitution (refR Γ⊢M∶A) validΔ σ∶Δ⟶Γ = refR (substitution Γ⊢M∶A validΔ σ∶Δ⟶Γ)
substitution (⊃*R Γ⊢P∶φ≡φ' Γ⊢Q∶ψ≡ψ') validΔ σ∶Δ⟶Γ = 
  ⊃*R (substitution Γ⊢P∶φ≡φ' validΔ σ∶Δ⟶Γ) (substitution Γ⊢Q∶ψ≡ψ' validΔ σ∶Δ⟶Γ)
substitution (univR Γ⊢δ∶φ⊃ψ Γ⊢ε∶ψ⊃φ) validΔ σ∶Δ⟶Γ = 
  univR (substitution Γ⊢δ∶φ⊃ψ validΔ σ∶Δ⟶Γ) (substitution Γ⊢ε∶ψ⊃φ validΔ σ∶Δ⟶Γ)
substitution (plusR Γ⊢P∶φ≡φ') validΔ σ∶Δ⟶Γ = plusR (substitution Γ⊢P∶φ≡φ' validΔ σ∶Δ⟶Γ)
substitution (minusR Γ⊢P∶φ≡ψ) validΔ σ∶Δ⟶Γ = minusR (substitution Γ⊢P∶φ≡ψ validΔ σ∶Δ⟶Γ)
substitution (lllR {B = B} {M = M} {N = N} Γ⊢M∶A⇛B Γ⊢N∶A⇛B ΓAAE⊢P∶Mx≡Ny) validΔ σ∶Δ⟶Γ = 
  lllR (substitution Γ⊢M∶A⇛B validΔ σ∶Δ⟶Γ) 
    (substitution Γ⊢N∶A⇛B validΔ σ∶Δ⟶Γ) 
    (change-type (substitution ΓAAE⊢P∶Mx≡Ny 
      (valid-addpath validΔ) (liftSub-typed (liftSub-typed (liftSub-typed σ∶Δ⟶Γ (ctxTR validΔ)) (ctxTR (ctxTR validΔ))) (valid-addpath validΔ))) 
  (cong₂ (λ x y → appT x (var x₂) ≡〈 B 〉 appT y (var x₁)) 
    (liftSub-upRep₃ M) (liftSub-upRep₃ N)))
substitution (appER Γ⊢N∶A Γ⊢N'∶A Γ⊢P∶M≡M' Γ⊢Q∶N≡N') validΔ σ∶Δ⟶Γ = 
  appER (substitution Γ⊢N∶A validΔ σ∶Δ⟶Γ) (substitution Γ⊢N'∶A validΔ σ∶Δ⟶Γ) 
    (substitution Γ⊢P∶M≡M' validΔ σ∶Δ⟶Γ) (substitution Γ⊢Q∶N≡N' validΔ σ∶Δ⟶Γ)
substitution (convER Γ⊢P∶M≡N Γ⊢M'∶A Γ⊢N'∶A M≃M' N≃N') validΔ σ∶Δ⟶Γ = 
  convER (substitution Γ⊢P∶M≡N validΔ σ∶Δ⟶Γ) (substitution Γ⊢M'∶A validΔ σ∶Δ⟶Γ) (substitution Γ⊢N'∶A validΔ σ∶Δ⟶Γ) (≃-resp-sub M≃M') (≃-resp-sub N≃N')

sub↖-typed : ∀ {U V} {σ : Sub U V} {Δ Γ A} → σ ∶ Δ ⟶ Γ → valid Δ → sub↖ σ ∶ addpath Δ A ⟶ Γ ,T A
sub↖-typed σ∶Δ⟶Γ validΔ x₀ = varR x₂ (valid-addpath validΔ)
sub↖-typed {σ = σ} {Δ} {Γ} {A} σ∶Δ⟶Γ validΔ (↑ x) = subst₂ (λ x₃ y → addpath Δ A ⊢ x₃ ∶ y) (rep-•R₃ (σ _ x)) (let open ≡-Reasoning in
  begin
    typeof x Γ ⟦ σ ⟧ 〈 upRep •R upRep •R upRep 〉
  ≡⟨ rep-•R₃ (typeof x Γ ⟦ σ ⟧) ⟩
    typeof x Γ ⟦ σ ⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ sub↖-upRep {E = typeof x Γ} ⟩⟩
    typeof x Γ ⇑ ⟦ sub↖ σ ⟧
  ∎)
  (weakening (σ∶Δ⟶Γ x) (valid-addpath validΔ) (upRep₃-addpath-typed A))

sub↗-typed : ∀ {U V} {σ : Sub U V} {Δ Γ A} → σ ∶ Δ ⟶ Γ → valid Δ → sub↗ σ ∶ addpath Δ A ⟶ Γ ,T A
sub↗-typed σ∶Δ⟶Γ validΔ x₀ = varR x₁ (valid-addpath validΔ)
sub↗-typed {σ = σ} {Δ} {Γ} {A} σ∶Δ⟶Γ validΔ (↑ x) = subst₂ (λ x₃ y → addpath Δ A ⊢ x₃ ∶ y) (rep-•R₃ (σ _ x)) (let open ≡-Reasoning in
  begin
    typeof x Γ ⟦ σ ⟧ 〈 upRep •R upRep •R upRep 〉
  ≡⟨ rep-•R₃ (typeof x Γ ⟦ σ ⟧) ⟩
    typeof x Γ ⟦ σ ⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ sub↗-upRep {E = typeof x Γ} ⟩⟩
    typeof x Γ ⇑ ⟦ sub↗ σ ⟧
  ∎)
  (weakening (σ∶Δ⟶Γ x) (valid-addpath validΔ) (upRep₃-addpath-typed A))
