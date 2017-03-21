open import Grammar.Base

module Grammar.Substitution (G : Grammar) where
open import Grammar.Substitution.PreOpFamily G public
open import Grammar.Substitution.Lifting G public
open import Grammar.Substitution.RepSub G public
open import Grammar.Substitution.LiftFamily G public
open import Grammar.Substitution.OpFamily G public
open import Grammar.Substitution.BotSub G public
open import Grammar.Substitution.ExtendSub G public
