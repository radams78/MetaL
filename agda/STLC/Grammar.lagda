\begin{code}
module STLC.Grammar where

open import Grammar.Taxonomy
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
open Taxonomy stlcTaxonomy

type : ExpKind
type = nonVarKind -type

term : ExpKind
term = varKind -term
\end{code}
%</Taxonomy>