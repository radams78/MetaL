\AgdaHide{
\begin{code}
open import Grammar.Base

module Grammar.OpFamily.PreOpFamily (G : Grammar) where
open import Prelims.EqReasoning
open Grammar G
\end{code}
}

\subsection{Families of Operations}

Our aim here is to define the operations of \emph{replacement} and \emph{substitution}.  In order to organise this work, we introduce the following definitions.

A \emph{family of operations} over a grammar $G$ consists of:
\begin{enumerate}
\item
for any alphabets $U$ and $V$, a set $F[U,V]$ of \emph{operations} $\sigma$ from $U$ to $V$, $\sigma : U \rightarrow V$;
\item
for any operation $\sigma : U \rightarrow V$ and variable $x \in U$ of kind $K$, an expression $\sigma(x)$ over $V$ of kind $K$;
\item
for any alphabet $V$ and variable kind $K$, an operation $\uparrow : V \rightarrow (V , K)$, the \emph{lifting} operation;
\item
for any alphabet $V$, an operation $\id{V} : V \rightarrow V$, the \emph{identity} operation;
\item
for any operation $\sigma : U \rightarrow V$ and variable kind $K$, an operation $(\sigma , K) : (U , K) \rightarrow (V , K)$, the result of \emph{lifting} $\sigma$;
\item
for any operations $\rho : U \rightarrow V$ and $\sigma : V \rightarrow W$, an operation
$\sigma \circ \rho : U \rightarrow W$, the \emph{composition} of $\sigma$ and $\rho$;
\end{enumerate}
such that:
\begin{itemize}
\item
$\uparrow (x) \equiv x$
\item
$\id{V}(x) \equiv x$
\item
If $\rho \sim \sigma$ then $(\rho , K) \sim (\sigma , K)$
\item
$(\rho , K)(x_0) \equiv x_0$
\item
Given $\sigma : U \rightarrow V$ and $x \in U$, we have $(\sigma , K)(x) \equiv x$
\item
$(\sigma \circ \rho , K) \sim (\sigma , K) \circ (\rho , K)$
\item
$(\sigma \circ \rho)(x) \equiv \rho(x) [ \sigma ]$
\end{itemize}
where for $\sigma, \rho : U \rightarrow V$ we write $\sigma \sim \rho$ iff $\sigma(x) \equiv \rho(x)$ for all $x \in U$; and, given $\sigma : U \rightarrow V$ and $E$ an expression over $U$, we define $E[\sigma]$, the result of \emph{applying} the operation $\sigma$ to $E$, as follows:

\begin{align*}
x[\sigma] & \eqdef \sigma(x) \\
\lefteqn{c([\vec{x_1}] E_1, \ldots, [\vec{x_n}] E_n) [\sigma]} \\
 & \eqdef
c([\vec{x_1}] E_1 [(\sigma , K_{11}, \ldots, K_{1r_1})], \ldots,
[\vec{x_n}] E_n [(\sigma, K_{n1}, \ldots, K_{nr_n})])
\end{align*}
for $c$ a constructor of type (\ref{eq:conkind}).

\subsubsection{Pre-Families}
We formalize this definition in stages.  First, we define a \emph{pre-family of operations} to be a family with items of data 1--4 above that satisfies the first two axioms:

\begin{code}
record PreOpFamily : Set₂ where
  field
    Op : Alphabet → Alphabet → Set
    apV : ∀ {U} {V} {K} → Op U V → Var U K → Expression V (varKind K)
    up : ∀ {V} {K} → Op V (V , K)
    apV-up : ∀ {V} {K} {L} {x : Var V K} → apV (up {K = L}) x ≡ var (↑ x)
    idOp : ∀ V → Op V V
    apV-idOp : ∀ {V} {K} (x : Var V K) → apV (idOp V) x ≡ var x
\end{code}

This allows us to define the relation $\sim$, and prove it is an equivalence relation:

\begin{code}
  _∼op_ : ∀ {U} {V} → Op U V → Op U V → Set
  _∼op_ {U} {V} ρ σ = ∀ {K} (x : Var U K) → apV ρ x ≡ apV σ x
    
  ∼-refl : ∀ {U} {V} {σ : Op U V} → σ ∼op σ
  ∼-refl _ = refl
    
  ∼-sym : ∀ {U} {V} {σ τ : Op U V} → σ ∼op τ → τ ∼op σ
  ∼-sym σ-is-τ x = sym (σ-is-τ x)

  ∼-trans : ∀ {U} {V} {ρ σ τ : Op U V} → ρ ∼op σ → σ ∼op τ → ρ ∼op τ
  ∼-trans ρ-is-σ σ-is-τ x = trans (ρ-is-σ x) (σ-is-τ x)

  OP : Alphabet → Alphabet → Setoid _ _
  OP U V = record { 
     Carrier = Op U V ; 
     _≈_ = _∼op_ ; 
     isEquivalence = record { 
       refl = ∼-refl ; 
       sym = ∼-sym ; 
       trans = ∼-trans } }
\end{code}
