\begin{code}
module STLC.Grammar where

open import Data.List
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}

%<*Taxonomy>
\begin{code}
data stlcVarKind : Set where
  -term : stlcVarKind

data stlcNonVarKind : Set where
  -type : stlcNonVarKind

stlcTaxonomy : Taxonomy
stlcTaxonomy = record { 
  VarKind = stlcVarKind ; 
  NonVarKind = stlcNonVarKind }
\end{code}
%</Taxonomy>

\begin{code}
module STLCGrammar where
  open Taxonomy stlcTaxonomy
\end{code}

%<*Grammar>
\begin{code}
  type : ExpKind
  type = nonVarKind -type

  term : ExpKind
  term = varKind -term

  data stlcCon : ConKind → Set where
    -bot : stlcCon (type ✧)
    -arrow : stlcCon (type ✧ ⟶ type ✧ ⟶ type ✧)
    -app : stlcCon (term ✧ ⟶ term ✧ ⟶ term ✧)
    -lam : stlcCon (type ✧ ⟶ (-term ⟶ term ✧) ⟶ term ✧)

  stlcParent : VarKind → ExpKind
  stlcParent -term = type

  stlc : Grammar
  stlc = record { 
    taxonomy = stlcTaxonomy ; 
    isGrammar = record { 
      Con = stlcCon ; 
      parent = stlcParent } }
\end{code}

\AgdaHide{
\begin{code}
open STLCGrammar
open Grammar STLCGrammar.stlc
\end{code}
}

\begin{code}
Type : Alphabet → Set
Type V = Expression V type

Term : Alphabet → Set
Term V = Expression V term

⊥ : ∀ V → Type V
⊥ V = app -bot []

_⇒_ : ∀ {V} → Type V → Type V → Type V
A ⇒ B = app -arrow (A ∷ B ∷ [])

appl : ∀ {V} → Term V → Term V → Term V
appl M N = app -app (M ∷ N ∷ [])

Λ : ∀ {V} → Type V → Term (V , -term) → Term V
Λ A M = app -lam (A ∷ M ∷ [])
\end{code}
%</Grammar>