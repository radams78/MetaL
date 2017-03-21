-- Project: Canonicity of PHOML
-- Author:  Robin Adams
-- Module:  Grammar
--------------------------------------------------------------
-- A grammar or syntax with binding
--------------------------------------------------------------

-- Definition of a taxonomy
open import Grammar.Taxonomy public

-- Definition of a grammar over a taxonomy
open import Grammar.Base public

module Grammar (G : Grammar) where
open Grammar G public

-- A family of operations (replacement or substitution)
open import Grammar.OpFamily G public

-- Replacement of variables for variables
open import Grammar.Replacement G public

-- Replacement as a functor from sets to sets
open import Grammar.Replacement.SetFunctor G public

-- Substitution of terms for variables
open import Grammar.Substitution G public

-- Contexts
open import Grammar.Context G public
