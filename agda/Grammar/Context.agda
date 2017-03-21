open import Grammar.Base

module Grammar.Context (G : Grammar) where

open import Data.Nat
open import Data.Fin
open import Prelims
open Grammar G
open import Grammar.Replacement G

infixl 55 _,_
data Context : Alphabet → Set where
  〈〉 : Context ∅
  _,_ : ∀ {V} {K} → Context V → Expression V (parent K) → 
    Context (V , K)

-- Define typeof such that, if x : A ∈ Γ, then typeof x Γ ≡ A
-- We define it the following way so that typeof x Γ computes to an expression of the form
-- M 〈 upRep 〉, even if x is not in canonical form
pretypeof : ∀ {V} {K} {L} (x : Var (V , K) L) (Γ : Context (V , K)) → Expression V (parent L)
typeof : ∀ {V} {K} (x : Var V K) (Γ : Context V) → Expression V (parent K)

pretypeof x₀ (Γ , A) = A
pretypeof (↑ x) (Γ , A) = typeof x Γ

typeof {∅} ()
typeof {_ , _} x Γ = pretypeof x Γ ⇑

_∶_⇒R_ : ∀ {U} {V} → Rep U V → Context U → Context V → Set
ρ ∶ Γ ⇒R Δ = ∀ {K} x → typeof (ρ K x) Δ ≡ typeof x Γ 〈 ρ 〉

infix 25 _,,_
_,,_ : ∀ {V} {AA} → Context V → Types V AA → Context (extend V AA)
Γ ,, [] = Γ
Γ ,, (A , AA) = (Γ , A) ,, AA

{- infix 25 _,,,_
_,,,_ : ∀ {V AA} → Context V → snocTypes V AA → Context (extend SNOCLIST V AA)
Γ ,,, [] = Γ
Γ ,,, (AA snoc A) = (Γ ,,, AA) , A -}

idRep-typed : ∀ {V} {Γ : Context V} → idRep V ∶ Γ ⇒R Γ
idRep-typed _ = ≡-sym rep-idRep

upRep-typed : ∀ {V Γ K} (A : Expression V (parent K)) → upRep ∶ Γ ⇒R (Γ , A)
upRep-typed _ _ = refl

liftRep-typed : ∀ {U V ρ K} {Γ : Context U} {Δ : Context V} {A : Expression U (parent K)} → 
  ρ ∶ Γ ⇒R Δ → liftRep K ρ ∶ (Γ , A) ⇒R (Δ , A 〈 ρ 〉)
liftRep-typed {A = A} ρ∶Γ⇒Δ x₀ = ≡-sym (liftRep-upRep A)
liftRep-typed {ρ = ρ} {K} {Γ} {Δ} {A} ρ∶Γ⇒Δ {L} (↑ x) = let open ≡-Reasoning in 
  begin
    typeof (ρ L x) Δ ⇑
  ≡⟨ rep-congl (ρ∶Γ⇒Δ x) ⟩
    typeof x Γ 〈 ρ 〉 ⇑
  ≡⟨⟨ liftRep-upRep (typeof x Γ) ⟩⟩
    (typeof x Γ ⇑) 〈 liftRep K ρ 〉
  ∎

liftsRep-typed : ∀ {U V ρ KK} {Γ : Context U} {Δ : Context V} {AA : Types U KK} →
  ρ ∶ Γ ⇒R Δ → liftsRep KK ρ ∶ (Γ ,, AA) ⇒R (Δ ,, Types-rep AA ρ)
liftsRep-typed {AA = []} ρ∶Γ⇒RΔ = ρ∶Γ⇒RΔ
liftsRep-typed {AA = A , AA} ρ∶Γ⇒RΔ = liftsRep-typed {AA = AA} (liftRep-typed ρ∶Γ⇒RΔ)

•R-typed : ∀ {U V W} {σ : Rep V W} {ρ : Rep U V} {Γ} {Δ} {Θ} → 
  σ ∶ Δ ⇒R Θ → ρ ∶ Γ ⇒R Δ → (σ •R ρ) ∶ Γ ⇒R Θ
•R-typed {U} {V} {W} {σ} {ρ} {Γ} {Δ} {Θ} σ∶Δ⇒RΘ ρ∶Γ⇒RΔ {K} x = let open ≡-Reasoning in 
  begin
    typeof (σ K (ρ K x)) Θ
  ≡⟨ σ∶Δ⇒RΘ (ρ K x) ⟩
    typeof (ρ K x) Δ 〈 σ 〉
  ≡⟨ rep-congl (ρ∶Γ⇒RΔ x) ⟩
    typeof x Γ 〈 ρ 〉 〈 σ 〉
  ≡⟨⟨ rep-•R (typeof x Γ) ⟩⟩
    typeof x Γ 〈 σ •R ρ 〉
  ∎

upRep₃-typed : ∀ {V K1 K2 K3} {Γ : Context V} 
  {A1 : Expression V (parent K1)} {A2 : Expression (V , K1) (parent K2)} {A3 : Expression ((V , K1) , K2) (parent K3)} → 
  (upRep •R upRep) •R upRep ∶ Γ ⇒R (((Γ , A1) , A2) , A3)
upRep₃-typed {V} {Γ = Γ} {A1} {A2} {A3} = 
  •R-typed {Θ = ((Γ , A1) , A2) , A3} 
  (•R-typed {Θ = ((Γ , A1) , A2) , A3} (upRep-typed A3) (upRep-typed A2)) (upRep-typed A1)

