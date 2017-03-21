\begin{code}
module Grammar.Taxonomy where
open import Data.List
open import Prelims

--A taxonomy consists of a set of expression kinds, 
--divided into variable kinds and non-variable kinds
\end{code}

%<*Taxonomy>
\begin{code}
record Taxonomy : Set₁ where
  field
    VarKind : Set
    NonVarKind : Set

  data ExpKind : Set where
    varKind : VarKind → ExpKind
    nonVarKind : NonVarKind → ExpKind
\end{code}
%</Taxonomy>

\begin{code}
-- An alphabet is a finite set of variables, each with an associated variable kind
  infixl 55 _,_
  data Alphabet : Set where
    ∅ : Alphabet
    _,_ : Alphabet → VarKind → Alphabet

-- Define concatenation of alphabets
-- TODO Extend alphabet with F VarKind for suitable functors F
  extend : Alphabet → List VarKind → Alphabet
  extend V [] = V
  extend V (K ∷ KK) = extend (V , K) KK

  snoc-extend : Alphabet → snocList VarKind → Alphabet
  snoc-extend V [] = V
  snoc-extend V (KK snoc K) = snoc-extend V KK , K

-- Define the set of variables of kind K in alphabet V
  data Var : Alphabet → VarKind → Set where
    x₀ : ∀ {V} {K} → Var (V , K) K
    ↑ : ∀ {V} {K} {L} → Var V L → Var (V , K) L

  x₁ : ∀ {V} {K} {L} → Var (V , K , L) K
  x₁ = ↑ x₀

  x₂ : ∀ {V} {K} {L} {L'} → Var (V , K , L , L') K
  x₂ = ↑ x₁

-- A simple kind over sets A and B is an expression of the form
-- a1 ⟶ a2 ⟶ ... ⟶ an ⟶ b ✧
-- where each ai is in A and b is in B
  record SimpleKind (A B : Set) : Set where
    constructor SK
    field
      dom : List A
      cod : B

  infix 71 _✧
  _✧ : ∀ {A} {B} → B → SimpleKind A B
  b ✧ = SK [] b

  infixr 70 _⟶_
  _⟶_ : ∀ {A} {B} → A → SimpleKind A B → SimpleKind A B
  a ⟶ SK dom cod = SK (a ∷ dom) cod

-- An abstraction kind is a kind of the form
-- K1 ⟶ ... ⟶ Kn ⟶ L
-- Ki a variable kind, L an expression kind

-- A constructor kind is a kind of the form
-- A1 ⟶ ... ⟶ An ⟶ K
-- Ai an abstraction kind, K an expression kind
  AbsKind = SimpleKind VarKind ExpKind
  ConKind = SimpleKind AbsKind ExpKind

-- A kind is either an expression kind or a list of abstraction kinds
  data KindClass : Set where
    -Expression : KindClass
    -ListAbs : KindClass

  Kind : KindClass → Set
  Kind -Expression = ExpKind
  Kind -ListAbs = List AbsKind
\end{code}