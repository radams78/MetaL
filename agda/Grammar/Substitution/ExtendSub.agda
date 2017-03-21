open import Grammar.Base
module Grammar.Substitution.ExtendSub (G : Grammar) where
open import Prelims.EqReasoning
open Grammar G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.OpFamily G
open import Grammar.Substitution.BotSub G

extendSub : ∀ {U} {V} {K} → Sub U V → Expression V (varKind K) → Sub (U , K) V
extendSub σ M _ x₀ = M
extendSub σ M _ (↑ x) = σ _ x

extendSub-decomp' : ∀ {U V K} {σ : Sub U V} {E : VExpression V K} →
  extendSub σ E ∼ x₀:= E • liftSub _ σ
extendSub-decomp' x₀ = refl
extendSub-decomp' {σ = σ} (↑ x) = ≡-sym (botSub-upRep (σ _ x))

extendSub-decomp : ∀ {U} {V} {σ : Sub U V} {K} {M : Expression V (varKind K)} {C} {L} (E : Subexp (U , K) C L) →
  E ⟦ extendSub σ M ⟧ ≡ E ⟦ liftSub K σ ⟧ ⟦ x₀:= M ⟧
extendSub-decomp {σ = σ} {K} {M} E = let open ≡-Reasoning in
  begin
    E ⟦ extendSub σ M ⟧
  ≡⟨ sub-congr E extendSub-decomp' ⟩
    E ⟦ x₀:= M • liftSub K σ ⟧
  ≡⟨ sub-• E ⟩
    E ⟦ liftSub K σ ⟧ ⟦ x₀:= M ⟧
  ∎

•-botsub : ∀ {U V K} {σ : Sub U V} {N : VExpression U K} → σ • (x₀:= N) ∼ extendSub σ (N ⟦ σ ⟧)
•-botsub x₀ = refl
•-botsub (↑ _) = refl

extendSub-upRep : ∀ {U V C K L} (E : Subexp U C K) {σ : Sub U V} {F : VExpression V L} → E ⇑ ⟦ extendSub σ F ⟧ ≡ E ⟦ σ ⟧
extendSub-upRep {U} {V} {C} {K} {L} E {σ} {F} = let open ≡-Reasoning in 
  begin
    E ⇑ ⟦ extendSub σ F ⟧
  ≡⟨ extendSub-decomp (E ⇑) ⟩
    E ⇑ ⟦ liftSub L σ ⟧ ⟦ x₀:= F ⟧
  ≡⟨ sub-congl (liftSub-upRep E) ⟩
    E ⟦ σ ⟧ ⇑ ⟦ x₀:= F ⟧
  ≡⟨ botSub-upRep (E ⟦ σ ⟧) ⟩
    E ⟦ σ ⟧
  ∎
  
