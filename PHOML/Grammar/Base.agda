module PHOML.Grammar.Base where
open import Data.List
open import Grammar.Taxonomy
open import Grammar.Base

data PHOMLVarKind : Set where
  -Proof : PHOMLVarKind
  -Term : PHOMLVarKind
  -Path : PHOMLVarKind

data PHOMLNonVarKind : Set where
  -Type : PHOMLNonVarKind
  -Equation : PHOMLNonVarKind

PHOMLTaxonomy : Taxonomy
PHOMLTaxonomy = record { 
  VarKind = PHOMLVarKind; 
  NonVarKind = PHOMLNonVarKind }

module PHOMLgrammar where
  open Taxonomy PHOMLTaxonomy

  -vProof : ExpKind
  -vProof = varKind -Proof

  -vTerm : ExpKind
  -vTerm = varKind -Term

  -vPath : ExpKind
  -vPath = varKind -Path

  -nvType : ExpKind
  -nvType = nonVarKind -Type

  -nvEq : ExpKind
  -nvEq = nonVarKind -Equation

  infix 25 _⇛_
  data Type : Set where
    Ω : Type
    _⇛_ : Type → Type → Type

  data Dir : Set where
    -plus : Dir
    -minus : Dir

  pathDom : List VarKind
  pathDom = -Term ∷ -Term ∷ -Path ∷ []

  data PHOMLcon : ConKind → Set where
    -ty : Type → PHOMLcon (-nvType ✧)
    -bot : PHOMLcon (-vTerm ✧)
    -imp : PHOMLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vTerm ✧)
    -lamTerm : Type → PHOMLcon ((-Term ⟶ -vTerm ✧) ⟶ -vTerm ✧)
    -appTerm : PHOMLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vTerm ✧)
    -lamProof : PHOMLcon (-vTerm ✧ ⟶ (-Proof ⟶ -vProof ✧) ⟶ -vProof ✧)
    -appProof : PHOMLcon (-vProof ✧ ⟶ -vProof ✧ ⟶ -vProof ✧)
    -dir : Dir → PHOMLcon (-vPath ✧ ⟶ -vProof ✧)
    -ref : PHOMLcon (-vTerm ✧ ⟶ -vPath ✧)
    -imp* : PHOMLcon (-vPath ✧ ⟶ -vPath ✧ ⟶ -vPath ✧)
    -univ : PHOMLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vProof ✧ ⟶ -vProof ✧ ⟶ -vPath ✧)
    -lll : Type → PHOMLcon (SK pathDom -vPath ⟶ -vPath ✧)
    -app* : PHOMLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -vPath ✧ ⟶ -vPath ✧ ⟶ -vPath ✧)
    -eq : Type → PHOMLcon (-vTerm ✧ ⟶ -vTerm ✧ ⟶ -nvEq ✧)

  PHOMLparent : PHOMLVarKind → ExpKind
  PHOMLparent -Proof = -vTerm
  PHOMLparent -Term = -nvType
  PHOMLparent -Path = -nvEq

  PHOML : Grammar
  PHOML = record { 
    taxonomy = PHOMLTaxonomy;
    isGrammar = record { 
      Con = PHOMLcon; 
      parent = PHOMLparent } }
