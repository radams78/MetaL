\begin{code}
open import Grammar.Base

module Grammar.Pattern (G : Grammar) where
open import Data.List hiding (concat)

open Grammar G

open import Grammar.Replacement G
open import Grammar.Substitution G

infixl 55 _,_
data SecondOrderAlphabet : Set where
  ∅ : SecondOrderAlphabet
  _,_ : SecondOrderAlphabet → AbstractionKind → SecondOrderAlphabet

data Metavar : SecondOrderAlphabet → AbstractionKind → Set where
  X₀ : ∀ {V} {K} → Metavar (V , K) K
  ↑  : ∀ {V K L} → Metavar V L → Metavar (V , K) L

data Pattern (U : SecondOrderAlphabet) (V : Alphabet) : ExpressionKind → Set
Abstraction2 : ∀ (U : SecondOrderAlphabet) (V : Alphabet) → AbstractionKind → Set
data ListPattern (U : SecondOrderAlphabet) (V : Alphabet) : List VariableKind → Set
data ListPattern2 (U : SecondOrderAlphabet) (V : Alphabet) : List AbstractionKind → Set

data Pattern U V where
  var : ∀ {K} → Var V K → Pattern U V (varKind K)
  metavar : ∀ {KK L} → Metavar U (SK KK L) → ListPattern U V KK → Pattern U V L
  app : ∀ {AA K} → Con (SK AA K) → ListPattern2 U V AA → Pattern U V K
  --TODO Rename varKind to variableKind

Abstraction2 U V (SK KK L) = Pattern U (extend V KK) L

data ListPattern U V where
  [] : ListPattern U V []
  _∷_ : ∀ {K KK} → Pattern U V (varKind K) → ListPattern U V KK → ListPattern U V (K ∷ KK)

data ListPattern2 U V where
  [] : ListPattern2 U V []
  _∷_ : ∀ {A AA} → Abstraction2 U V A → ListPattern2 U V AA → ListPattern2 U V (A ∷ AA)

Instantiation : SecondOrderAlphabet → Alphabet → Set
Instantiation U V = ∀ A → Metavar U A → Abstraction V A

_•RI_ : ∀ {U V W} → Rep V W → Instantiation U V → Instantiation U W
(ρ •RI τ) (SK KK _) X = τ (SK KK _) X ⟨ liftsRep KK ρ ⟩

concat : Alphabet → Alphabet → Alphabet
concat U ∅ = U
concat U (V , K) = concat U V , K

embedl : ∀ {U} V → Rep U (concat U V)
embedl ∅ x = x
embedl (V , K) x = ↑ (embedl V x)

embedr : ∀ {U V} → Rep V (concat U V)
embedr x₀ = x₀
embedr (↑ x) = ↑ (embedr x)

data  ListExpression (V : Alphabet) : List VariableKind → Set where
  [] : ListExpression V []
  _∷_ : ∀ {KK K} → Expression V (varKind K) → ListExpression V KK → ListExpression V (K ∷ KK)

repLE : ∀ {U V KK} → ListExpression U KK → Rep U V → ListExpression V KK
repLE [] _ = []
repLE (E ∷ EE) ρ = E ⟨ ρ ⟩ ∷ repLE EE ρ

botSub' : ∀ {V KK} → ListExpression V KK → Sub (extend V KK) V
botSub' [] = idSub _
botSub' {V} {K ∷ KK} (E ∷ EE) = x₀:= E • botSub' {V , K} (repLE EE ↑)

apply : ∀ {V KK L} → Abstraction V (SK KK L) → ListExpression V KK → Expression V L
apply {V} {KK} {L} E FF = E ⟦ botSub' FF ⟧

instantiate : ∀ {U V W K} → Instantiation U W → Rep V W → Pattern U V K → Expression W K
instantiateAbs : ∀ {U V W A} → Instantiation U W → Rep V W → Abstraction2 U V A → Abstraction W A
instantiateList : ∀ {U V W KK} → Instantiation U W → Rep V W → ListPattern U V KK → ListExpression W KK
instantiateList2 : ∀ {U V W AA} → Instantiation U W → Rep V W → ListPattern2 U V AA → ListAbstraction W AA

instantiate τ ρ (var x) = var (ρ x)
instantiate τ ρ (metavar X EE) = apply (τ _ X) (instantiateList τ ρ EE)
instantiate τ ρ (app c EE) = app c (instantiateList2 τ ρ EE)

instantiateAbs {A = SK KK _} τ ρ E = instantiate (ups' KK •RI τ) (liftsRep KK ρ) E

instantiateList _ _ [] = []
instantiateList τ ρ (E ∷ EE) = instantiate τ ρ E ∷ instantiateList τ ρ EE

instantiateList2 _ _ [] = []
instantiateList2 {AA = A ∷ _} τ ρ (E ∷ EE) = instantiateAbs {A = A} τ ρ E ∷ instantiateList2 τ ρ EE
\end{code}
