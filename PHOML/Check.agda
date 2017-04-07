module PHOPL.Check where
open import Prelims
open import PHOPL.Grammar
open import PHOPL.PathSub
open import PHOPL.Meta

data _⇒_ : ∀ {V K} → VExpression V K → VExpression V K → Set where
  β    : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ⇒ M ⟦ x₀:= N ⟧
  appl : ∀ {V} {M M' N : Term V} → M ⇒ M' → appT M N ⇒ appT M' N
  Λ    : ∀ {V A} {M N : Term (V , -Term)} → M ⇒ N → ΛT A M ⇒ ΛT A N
  βP   : ∀ {V} {M N : Term V} {A P Q} → app* M N (λλλ A P) Q ⇒ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  app*l : ∀ {V} {M N : Term V} {P P' Q} → P ⇒ P' → app* M N P Q ⇒ app* M N P' Q
  λλλr  : ∀ {V A} {P Q : Path (V , -Term , -Term , -Path)} → P ⇒ Q → λλλ A P ⇒ λλλ A Q

red-resp-pathSub : ∀ {U V} {M N : Term V} {τ : PathSub V U} {ρ σ} → 
  M ⇒ N → (_⇒_ {U} { -Path} (M ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧))
red-resp-pathSub {U} {τ = τ} {ρ} {σ} (β {V} {A} {M} {N}) = 
  subst
    (λ x →
       app* (N ⟦ ρ ⟧) (N ⟦ σ ⟧)
       (λλλ A (M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧))
       (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧)
       ⇒ x)
  (let open ≡-Reasoning in
  begin
    M ⟦⟦ liftPathSub τ ∶ sub↖ ρ ∼ sub↗ σ ⟧⟧ ⟦ x₂:= N ⟦ ρ ⟧ ,x₁:= N ⟦ σ ⟧ ,x₀:= N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧ ⟧
  ≡⟨⟨ pathsub-extendPS M ⟩⟩
    M ⟦⟦ extendPS τ (N ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧) ∶ extendSub ρ (N ⟦ ρ ⟧) ∼ extendSub σ (N ⟦ σ ⟧) ⟧⟧
  ≡⟨⟨ pathSub-cong M •PS-botsub •-botsub •-botsub ⟩⟩
    M ⟦⟦ τ ∶ ρ ≡ σ •PS (x₀:= N) ∶ ρ • (x₀:= N) ∼ σ • (x₀:= N) ⟧⟧
  ≡⟨⟨ pathsub-sub M ⟩⟩
    M ⟦ x₀:= N ⟧ ⟦⟦ τ ∶ ρ ∼ σ ⟧⟧
  ∎) 
  βP
red-resp-pathSub (appl M⇒M') = app*l (red-resp-pathSub M⇒M')
red-resp-pathSub (Λ M⇒N) = λλλr (red-resp-pathSub M⇒N)
