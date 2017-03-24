\begin{code}
{- Metavariable conventions:
  A, B    range over abstraction kinds
  C       range over kind classes
  AA, BB  range over lists of abstraction kinds
  E, F, G range over subexpressions
  K, L    range over expression kinds including variable kinds
  M, N, P range over expressions
  U, V, W range over alphabets -}
open import Data.List
open import Prelims
open import Grammar.Taxonomy

module Grammar.Base where

--A grammar over a taxonomy consists of a set of constructors for each constructor kind,
--and a function assigning a parent to each variable kind
--Intention: for each declaration x : A, x is of some variable kind V,
--and the kind of A is the parent of V
\end{code}

%<*Grammar>
\begin{code}
record IsGrammar (T : Taxonomy) : Set₁ where
  open Taxonomy T
  field
    Con    : ConstructorKind → Set
    parent : VariableKind → ExpressionKind

record Grammar : Set₁ where
  field
    taxonomy : Taxonomy
    isGrammar : IsGrammar taxonomy
  open Taxonomy taxonomy public
  open IsGrammar isGrammar public
\end{code}
%</Grammar>

\begin{code}
--Define simultaneously:
--An expression of kind K is either a variable of kind K,
--or a constructor of kind AA → K applied to a list of abstractions of kinds given by AA
--An abstraction of kind KK → L is an expression of kind L in an alphabet extended by
--variables of kinds given by KK
  data Subexp (V : Alphabet) : ∀ C → Kind C → Set
  Expression : Alphabet → ExpressionKind → Set
  VExpression : Alphabet → VariableKind → Set
  Abstraction : Alphabet → AbstractionKind → Set
  ListAbstraction : Alphabet → List AbstractionKind → Set

  Expression V K = Subexp V -Expression K
  VExpression V K = Expression V (varKind K)
  Abstraction V (SK KK L) = Expression (extend V KK) L
  ListAbstraction V AA = Subexp V -ListAbstraction AA

  infixr 5 _∷_
  data Subexp V where
    var : ∀ {K} → Var V K → VExpression V K
    app : ∀ {AA} {K} → Con (SK AA K) → ListAbstraction V AA → Expression V K
    [] : ListAbstraction V []
    _∷_ : ∀ {A} {AA} → Abstraction V A → ListAbstraction V AA → ListAbstraction V (A ∷ AA)

--The mapping from variables to expressions is injective
  var-inj : ∀ {V} {K} {x y : Var V K} → var x ≡ var y → x ≡ y
  var-inj refl = refl

--Given a list of variable kinds K1, ..., Kn, 
--let Types [K1 ... Kn] be the set of all lists [A1 ... An]
--such that Ai is of kind the parent of Ki
--I.e. such that x1 : A1, ..., xn : An is a well-formed context
--where xi has kind Ki
  data Types : Alphabet → List VariableKind → Set where
    [] : ∀ {V} → Types V []
    _,_ : ∀ {V K AA} → Expression V (parent K) → Types (V , K) AA → Types V (K ∷ AA)

  data snocTypes : Alphabet → snocList VariableKind → Set where
    [] : ∀ {V} → snocTypes V []
    _snoc_ : ∀ {V AA K} → snocTypes V AA → Expression (snoc-extend V AA) (parent K) → snocTypes V (AA snoc K)
\end{code}