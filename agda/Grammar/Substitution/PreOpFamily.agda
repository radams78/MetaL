open import Grammar.Base

module Grammar.Substitution.PreOpFamily (G : Grammar) where
open import Data.List
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G

Sub : Alphabet → Alphabet → Set
Sub U V = ∀ {K} → Var U K → VExpression V K

upSub : ∀ {V} {K} → Sub V (V , K)
upSub x = var (↑ x)

pre-substitution : PreOpFamily
pre-substitution = record { 
  Op = Sub; 
  apV = λ σ → σ; 
  up = upSub;
  apV-up = refl; 
  idOp = λ _ → var; 
  apV-idOp = λ _ → refl }

open PreOpFamily pre-substitution using () renaming (_∼op_ to _∼_;idOp to idSub) public

