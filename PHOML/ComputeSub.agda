module PHOML.ComputeSub where
open import Prelims.EqReasoning
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Compute

⊧S_∶_ : ∀ {U V} → Sub U V → Context U → Set
⊧S σ ∶ Γ = ∀ {K} x → ⊧ σ K x ∶ (typeof x Γ) ⟦ σ ⟧

⊧S-cong : ∀ {U V} {σ σ' : Sub U V} {Γ : Context U} → ⊧S σ ∶ Γ → σ ∼ σ' → ⊧S σ' ∶ Γ
⊧S-cong {Γ = Γ} ⊧σ∶Γ σ∼σ' x = subst₂ ⊧_∶_ (σ∼σ' x) (sub-congr (typeof x Γ) σ∼σ') (⊧σ∶Γ x)

⊧_∶_≡_∶_ : ∀ {U V} → PathSub U V → Sub U V → Sub U V → Context U → Set
⊧ τ ∶ ρ ≡ σ ∶ Γ = ∀ x → ⊧E τ x ∶ ρ -Term x ≡〈 yt (typeof x Γ) 〉 σ -Term x

⊧RS : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} {Γ : Context U} → ⊧S σ ∶ Γ → ⊧S ρ •RS σ ∶ Γ
⊧RS {U} {V} {W} {ρ = ρ} {σ = σ} {Γ} ⊧σ∶Γ x = subst (λ y → ⊧ σ _ x 〈 ρ 〉 ∶ y) (≡-sym (sub-•RS (typeof x Γ))) (⊧rep {E = σ _ x} (⊧σ∶Γ x))

⊧RP : ∀ {U V W} {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} {Γ : Context U} →
  ⊧ τ ∶ σ ≡ σ' ∶ Γ → ⊧ ρ •RP τ ∶ ρ •RS σ ≡ ρ •RS σ' ∶ Γ
⊧RP {U} {V} {W} {ρ} {τ} {σ} {σ'} {Γ} ⊧τ∶σ≡σ' x = ⊧Erep (⊧τ∶σ≡σ' x)

⊧extendSub : ∀ {U V K} {σ : Sub U V} {Γ} {E : VExpression V K} {T : Expression U (parent K)} → ⊧S σ ∶ Γ → ⊧ E ∶ T ⟦ σ ⟧ → ⊧S extendSub σ E ∶ (Γ , T)
⊧extendSub {E = E} {T} ⊧σ∶Γ ⊧E∶T x₀ = subst (λ x → ⊧ E ∶ x) (sub-•SR T) ⊧E∶T
⊧extendSub {σ = σ} {Γ} ⊧σ∶Γ ⊧E∶T (↑ x) = subst (λ y → ⊧ σ _ x ∶ y) (sub-•SR (typeof x Γ)) (⊧σ∶Γ x)

⊧extendSub' : ∀ {U V K} {σ : Sub U V} {Γ} {E : VExpression V K} {T : Expression U (parent K)} → ⊧S σ ∶ Γ → ⊧ E ∶ T ⟦ σ ⟧ → ⊧S x₀:= E • liftSub K σ ∶ (Γ , T)
⊧extendSub' {E = E} {T} ⊧σ∶Γ ⊧E∶T = ⊧S-cong (⊧extendSub ⊧σ∶Γ ⊧E∶T) extendSub-decomp'

⊧extend : ∀ {U V} {Q : Path V} {N N'} {σ : Sub U V} {Γ A} → ⊧S σ ∶ Γ → ⊧E Q ∶ N ≡〈 A 〉 N' → ⊧ x₀::= Q ∶ x₀:= N ≡ x₀:= N' •PS liftSub -Term σ ∶ x₀:= N • liftSub -Term σ ≡ x₀:= N' • liftSub -Term σ ∶ Γ ,T A
⊧extend ⊧σ∶Γ ⊧Q∶N≡N' x₀ = ⊧Q∶N≡N'
⊧extend {V = V} {Q = Q} {N} {N'} {σ = σ} {Γ} {A = A} ⊧σ∶Γ ⊧Q∶N≡N' (↑ x) = subst₄ ⊧E_∶_≡〈_〉_ 
  (let open ≡-Reasoning in 
  begin
    σ _ x ⟦⟦ refSub ∶ idSub V ≡ idSub V ⟧⟧
  ≡⟨ pathSub-cong (σ _ x) (∼∼-sym (botPathSub-upRep {P = Q})) (sub-sym (botSub-upRep' N)) (sub-sym (botSub-upRep' N')) ⟩
    σ _ x ⟦⟦ x₀::= Q •PR upRep ∶ x₀:= N •SR upRep ≡ x₀:= N' •SR upRep ⟧⟧
  ≡⟨⟨ pathSub-•PR (σ _ x) ⟩⟩
    σ _ x ⇑ ⟦⟦ x₀::= Q ∶ x₀:= N ≡ x₀:= N' ⟧⟧
  ∎) 
  (≡-sym (botSub-upRep (σ _ x))) 
  (let open ≡-Reasoning in 
  begin
    yt (typeof x Γ ⟦ σ ⟧)
  ≡⟨ yt-sub {A = typeof x Γ} ⟩
    yt (typeof x Γ)
  ≡⟨⟨ yt-rep (typeof x Γ) ⟩⟩
    yt (typeof x Γ ⇑)
  ∎)
  (≡-sym (botSub-upRep (σ _ x))) 
  (⊧σ∶Γ x)

⊧extendPS : ∀ {U V} {τ : PathSub U V} {ρ σ Γ P M A N} →
  ⊧ τ ∶ ρ ≡ σ ∶ Γ → ⊧E P ∶ M ≡〈 A 〉 N → ⊧ extendPS τ P ∶ extendSub ρ M ≡ extendSub σ N ∶ Γ ,T A
⊧extendPS ⊧τ∶ρ≡σ ⊧P∶M≡N x₀ = ⊧P∶M≡N
⊧extendPS {τ = τ} {ρ} {σ} {Γ} ⊧τ∶ρ≡σ ⊧P∶M≡N (↑ x) = subst (λ a → ⊧E τ x ∶ ρ _ x ≡〈 a 〉 σ _ x) (≡-sym (yt-rep (typeof x Γ))) (⊧τ∶ρ≡σ x)

