open import Grammar.Base

module Grammar.OpFamily (G : Grammar) where
open import Grammar.OpFamily.PreOpFamily G public
open import Grammar.OpFamily.Lifting G public
open import Grammar.OpFamily.LiftFamily G public
open import Grammar.OpFamily.Composition G public
open import Grammar.OpFamily.OpFamily G public
