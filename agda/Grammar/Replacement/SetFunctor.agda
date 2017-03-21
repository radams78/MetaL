open import Prelims
open import Grammar.Base

module Grammar.Replacement.SetFunctor (G : Grammar) where
open Grammar G
open import Grammar.Replacement G

record SetFunctor : Set₁ where
  field
    Fib : Alphabet → Set
    _〈〈_〉〉 : ∀ {U V} → Fib U → Rep U V → Fib V
    〈〈〉〉-id : ∀ {V} {a : Fib V} → a 〈〈 idRep V 〉〉 ≡ a
    〈〈〉〉-comp : ∀ {U V W} {ρ : Rep V W} {σ : Rep U V} {a : Fib U} → 
      a 〈〈 ρ •R σ 〉〉 ≡ a 〈〈 σ 〉〉 〈〈 ρ 〉〉

VAR : VarKind → SetFunctor
VAR K = record { 
  Fib = λ V → Var V K ; 
  _〈〈_〉〉 = λ x ρ → ρ K x ; 
  〈〈〉〉-id = refl ; 
  〈〈〉〉-comp = refl }

