open import Grammar.Base

module Grammar.Substitution.Lifting (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily.Lifting G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G

liftSub : ∀ {U} {V} K → Sub U V → Sub (U , K) (V , K)
liftSub _ _ _ x₀ = var x₀
liftSub _ σ K (↑ x) = (σ K x) 〈 upRep 〉

liftSub-cong : ∀ {U} {V} {K} {σ σ' : Sub U V} → 
  σ ∼ σ' → liftSub K σ ∼ liftSub K σ'
liftSub-cong {K = K} σ-is-σ' x₀ = refl
liftSub-cong σ-is-σ' (↑ x) = cong (λ E → E 〈 upRep 〉) (σ-is-σ' x)

LIFTSUB : Lifting pre-substitution
LIFTSUB = record { liftOp = liftSub ; liftOp-cong = liftSub-cong }

infix 70 _⟦_⟧
_⟦_⟧ : ∀ {U} {V} {C} {K} → 
  Subexp U C K → Sub U V → Subexp V C K
E ⟦ σ ⟧ = Lifting.ap LIFTSUB σ E

