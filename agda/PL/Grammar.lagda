\AgdaHide{
\begin{code}
module PL.Grammar where
open import Data.Empty
open import Data.List
open import Prelims
open import Grammar.Taxonomy
open import Grammar.Base
\end{code}
}

\section{Propositional Logic}

\subsection{Grammar}

The syntax of the system called \emph{propositional logic} is given by the following grammar.

\[ \begin{array}{lrcl}
\text{Proof} & \delta & ::= & p \mid \delta \delta \mid \lambda p : \phi . \delta \\
\text{Proposition} & φ & ::= & ⊥ \mid \phi \rightarrow \phi \\
\end{array} \]

\begin{code}
data PLVarKind : Set where
  -proof : PLVarKind

data PLNonVarKind : Set where
  -prp   : PLNonVarKind

PLtaxonomy : Taxonomy
PLtaxonomy = record { 
  VarKind = PLVarKind; 
  NonVarKind = PLNonVarKind }

module PLgrammar where
  open Taxonomy PLtaxonomy

  proof = varKind -proof
  prp = nonVarKind -prp

  data Prop : Set where
    ⊥P : Prop
    _⇛_ : Prop → Prop → Prop

  data PLCon : ConKind → Set where
    -prp : Prop → PLCon (prp ✧)
    -app : PLCon (proof ✧ ⟶ proof ✧ ⟶ proof ✧)
    -lam : Prop → PLCon ((-proof ⟶ proof ✧) ⟶ proof ✧)

  PLparent : VarKind → ExpKind
  PLparent -proof = prp

open PLgrammar

Propositional-Logic : Grammar
Propositional-Logic = record { 
  taxonomy = PLtaxonomy; 
  isGrammar = record { 
    Con = PLCon; 
    parent = PLparent } }

open import Grammar Propositional-Logic

unprp : ∀ {V} → Expression V prp → Prop
unprp (app (-prp φ) []) = φ

_,P_ : ∀ {P} → Context P → Prop → Context (P , -proof)
Γ ,P φ = _,_ {K = -proof} Γ (app (-prp φ) [])

Proof : Alphabet → Set
Proof P = Expression P proof

appP : ∀ {P} → Proof P → Proof P → Proof P
appP δ ε = app -app (δ ∷ ε ∷ [])

ΛP : ∀ {P} → Prop → Proof (P , -proof) → Proof P
ΛP φ δ = app (-lam φ) (δ ∷ [])
\end{code}

\subsubsection{$\beta$-reduction}

The relation of \emph{$\beta$-reduction} is defined by: $(\lambda x \delta) \epsilon
\rightarrow_\beta \delta [ x := \epsilon ]$.

\begin{code}
data β {V} : ∀ {K} {C} →
  Con (SK C K) → ListAbs V C → Expression V K → Set where
  βI : ∀ {φ} {δ} {ε} → β -app (ΛP φ δ ∷ ε ∷ []) (δ ⟦ x₀:= ε ⟧)

open import Reduction Propositional-Logic β
\end{code}

It is easy to check that $\beta$-reduction respects and creates replacement, and respects substitution.

\begin{code}
β-respects-rep : respects' REP
\end{code}

\AgdaHide{
\begin{code}
β-respects-rep (βI {δ = δ}) = 
  subst (β -app _) (sym (compRS-botSub δ)) βI
\end{code}
}

\begin{code}
β-creates-rep : creates' REP
\end{code}

\AgdaHide{
\begin{code}
β-creates-rep {c = -app} (var _ ∷ _) ()
β-creates-rep {c = -app} (app -app _ ∷ _) ()
β-creates-rep {c = -app} 
  (app (-lam _) (δ ∷ []) ∷ (ε ∷ [])) βI = record { 
  created = δ ⟦ x₀:= ε ⟧ ; 
  red-created = βI ; 
  ap-created = compRS-botSub δ }
β-creates-rep {c = -lam _} _ ()
β-creates-rep {c = -prp _} _ ()
\end{code}
}

\begin{code}
β-respects-sub : respects' SUB
\end{code}

\AgdaHide{
\begin{code}
β-respects-sub {σ = σ} (βI {φ} {δ} {ε}) = subst
  (β -app _) (sym (comp-botSub'' δ)) βI

red-β-redex : ∀ {P} {φ} {δ} {ε} {χ} (S : Proof P → Set) → 
    appP (ΛP φ δ) ε ⇒ χ →
    S (δ ⟦ x₀:= ε ⟧) →
    (∀ δ' → δ ⇒ δ' → S (appP (ΛP φ δ') ε)) →
    (∀ ε' → ε ⇒ ε' → S (appP (ΛP φ δ) ε')) →
    S χ
red-β-redex _ (redex βI) δ[p:=ε]∈S _ _ = δ[p:=ε]∈S
red-β-redex _ (app (appl (redex ()))) _ _ _
red-β-redex _ (app (appl (app (appl δ⇒δ')))) _ hyp1 _ = hyp1 _ δ⇒δ'
red-β-redex _ (app (appl (app (appr ())))) _ _ _
red-β-redex _ (app (appr (appl ε⇒ε'))) _ _ hyp2 = hyp2 _ ε⇒ε'
red-β-redex _ (app (appr (appr ()))) _ _ _
\end{code}
}

\subsubsection{Neutral Terms}

The \emph{neutral terms} are the variables and applications.

\begin{code}
data Neutral {P} : Proof P → Set where
  varNeutral : ∀ x → Neutral (var x)
  appNeutral : ∀ δ ε → Neutral (appP δ ε)
  
\end{code}

\begin{lemma}
If $\delta$ is neutral then $\delta \langle \rho \rangle$ is neutral.
\end{lemma}

\begin{code}
neutral-rep : ∀ {P} {Q} {δ : Proof P} {ρ : Rep P Q} → 
  Neutral δ → Neutral (δ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
neutral-rep {ρ = ρ} (varNeutral x) = varNeutral (ρ -proof x)
neutral-rep {ρ = ρ} (appNeutral δ ε) = appNeutral (δ 〈 ρ 〉) (ε 〈 ρ 〉)

NeutralC-lm : ∀ {P} {δ ε : Proof P} {X : Proof P → Set} →
  Neutral δ → 
  (∀ δ' → δ ⇒ δ' → X (appP δ' ε)) →
  (∀ ε' → ε ⇒ ε' → X (appP δ ε')) →
  ∀ χ → appP δ ε ⇒ χ → X χ
NeutralC-lm () _ _ ._ (redex βI)
NeutralC-lm _ hyp1 _ .(app -app (_∷_ _ (_∷_ _ []))) (app (appl δ→δ')) = hyp1 _ δ→δ'
NeutralC-lm _ _ hyp2 .(app -app (_∷_ _ (_∷_ _ []))) (app (appr (appl ε→ε'))) = hyp2 _ ε→ε'
NeutralC-lm _ _ _ .(app -app (_∷_ _ (_∷_ _ _))) (app (appr (appr ())))
\end{code}
}

