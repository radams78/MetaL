module PHOML.PathSub.RP where

infixr 75 _•RP_
_•RP_ : ∀ {U} {V} {W} → Rep V W → PathSub U V → PathSub U W
(ρ •RP τ) x = τ x 〈 ρ 〉

liftPathSub-•RP : ∀ {U V W} {τ : PathSub U V} {ρ : Rep V W} →
  liftPathSub (ρ •RP τ) ∼∼ liftsRep pathDom ρ •RP liftPathSub τ
liftPathSub-•RP x₀ = refl
liftPathSub-•RP {τ = τ} {ρ} (↑ x) = let open ≡-Reasoning in 
  begin
    τ x 〈 ρ 〉 ⇑ ⇑ ⇑
  ≡⟨⟨ liftRep-upRep₃ (τ x) ⟩⟩
    τ x ⇑ ⇑ ⇑ 〈 liftsRep pathDom ρ 〉
  ∎

--TODO Flip this
pathSub-•RP : ∀ {U} {V} {W} M {ρ : Rep V W} {τ : PathSub U V} {σ σ' : Sub U V} →
  M ⟦⟦ ρ •RP τ ∶ ρ •RS σ ≡ ρ •RS σ' ⟧⟧ ≡ M ⟦⟦ τ ∶ σ ≡ σ' ⟧⟧ 〈 ρ 〉
pathSub-•RP (var x) = refl
pathSub-•RP (app -bot []) = refl
pathSub-•RP (app -imp (φ ∷ ψ ∷ [])) = cong₂ _⊃*_ (pathSub-•RP φ) (pathSub-•RP ψ)
pathSub-•RP (app (-lamTerm A) (M ∷ [])) {ρ} {τ} {σ} {σ'} = cong (λλλ A) 
  (let open ≡-Reasoning in
  begin
    M ⟦⟦ liftPathSub (ρ •RP τ) ∶ sub↖ (ρ •RS σ) ≡ sub↗ (ρ •RS σ') ⟧⟧
  ≡⟨ pathSub-cong M liftPathSub-•RP sub↖-•RS sub↗-•RS ⟩
    M ⟦⟦ liftsRep pathDom ρ •RP liftPathSub τ ∶ liftsRep pathDom ρ •RS sub↖ σ ≡ liftsRep pathDom ρ •RS sub↗ σ' ⟧⟧
  ≡⟨ pathSub-•RP M ⟩
    M ⟦⟦ liftPathSub τ ∶ sub↖ σ ≡ sub↗ σ' ⟧⟧ 〈 liftsRep pathDom ρ 〉
  ∎)
pathSub-•RP (app -appTerm (M ∷ N ∷ [])) = cong₄ app* (sub-•RS N) (sub-•RS N) (pathSub-•RP M) (pathSub-•RP N)

