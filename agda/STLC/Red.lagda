\begin{code}
module STLC.Red where

open import STLC.Grammar
open import Grammar.Pattern stlc

--A reduction relation is a set of pairs of patterns
beta_alpha : SecondOrderAlphabet
beta_alpha = ∅ , type ✧ , -term ⟶ term ✧ , term ✧

A : Metavar beta_alpha (type ✧)
A = ↑ (↑ X₀)

M : Metavar beta_alpha (-term ⟶ term ✧)
M = ↑ X₀

N : Metavar beta_alpha (term ✧)
N = X₀

beta_left : Pattern beta_alpha ∅ term
beta_left = app -app (app -lam (metavar A [] ∷ metavar M (var x₀ ∷ []) ∷ []) ∷ metavar N [] ∷ [])

beta_right : Pattern beta_alpha ∅ term
beta_right = metavar M (metavar N [] ∷ [])


\end{code}
