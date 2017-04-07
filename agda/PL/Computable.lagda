\AgdaHide{
\begin{code}
--TODO Duplications with PHOPL.Computable
module PL.Computable where
open import Data.Empty
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import Prelims.Closure
open import PL.Grammar
open PLgrammar
open import Grammar Propositional-Logic
open import Reduction Propositional-Logic β
open import PL.Rules
\end{code}
}

\subsubsection{Computable Terms}

We define the sets of \emph{computable} proofs $C_\Gamma(\phi)$ for each context $\Gamma$ and proposition $\phi$ as follows:

\begin{align*}
C_\Gamma(\bot) & = \{ \delta \mid \Gamma \vdash \delta : \bot \text{ and } \delta \in SN \} \\
C_\Gamma(\phi \rightarrow \psi) & = \{ \delta \mid \Gamma : \delta : \phi \rightarrow \psi \text{ and } \forall \Delta ⊇ \Gamma . ∀ \epsilon \in C_\Delta(\phi). \delta \epsilon \in C_\Delta(\psi) \}
\end{align*}

\begin{code}
C : ∀ {P} → Context P → Prop → Proof P → Set
C Γ ⊥P δ = Γ ⊢ δ ∶ ⊥P × SN δ
C Γ (φ ⇛ ψ) δ = Γ ⊢ δ ∶ φ ⇛ ψ × 
  (∀ Q {Δ : Context Q} ρ ε → ρ ∶ Γ ⇒R Δ → 
    C Δ φ ε → C Δ ψ (appP (δ 〈 ρ 〉) ε))
\end{code}

\begin{lemma}$ $
\begin{enumerate}
\item
If $\delta \in C_\Gamma(\phi)$ then $\Gamma \vdash \delta : \phi$.

\begin{code}
C-typed : ∀ {P} {Γ : Context P} {φ} {δ} → C Γ φ δ → Γ ⊢ δ ∶ φ
\end{code}

\AgdaHide{
\begin{code}
C-typed {φ = ⊥P} = proj₁
C-typed {φ = _ ⇛ _} = proj₁
\end{code}
}

\item
If $\delta \in C_\Gamma(\phi)$ and $\rho : \Gamma \rightarrow \Delta$ then $\delta \langle \rho \rangle \in C_\Delta(\phi)$.

\begin{code}
C-rep : ∀ {P} {Q} {Γ : Context P} {Δ : Context Q} φ {δ} {ρ} → 
  C Γ φ δ → ρ ∶ Γ ⇒R Δ → C Δ φ (δ 〈 ρ 〉)
\end{code}

\AgdaHide{
\begin{code}
C-rep ⊥P (Γ⊢δ∶x₀ ,p SNδ) ρ∶Γ→Δ = (weakening Γ⊢δ∶x₀ ρ∶Γ→Δ) ,p SNrep β-creates-rep SNδ
C-rep {P} {Q} {Γ} {Δ} (φ ⇛ ψ) {δ} {ρ} (Γ⊢δ∶φ⇒ψ ,p Cδ) ρ∶Γ→Δ = 
  (weakening Γ⊢δ∶φ⇒ψ ρ∶Γ→Δ) ,p (λ R {Θ} σ ε σ∶Δ→Θ ε∈CΘ → subst (C Θ ψ) 
    (cong (λ x → appP x ε) (rep-comp δ))
    (Cδ R (σ •R ρ) ε (•R-typed {σ = σ} {ρ = ρ} ρ∶Γ→Δ σ∶Δ→Θ) ε∈CΘ))
\end{code}
}

\item
If $\delta \in C_\Gamma(\phi)$ and $\delta \twoheadrightarrow_\beta \epsilon$ then $\epsilon \in C_\Gamma(\phi)$.

\AgdaHide{
\begin{code}
C-osr : ∀ {P} {Γ : Context P} φ {δ} {ε} → C Γ φ δ → δ ⇒ ε → C Γ φ ε
C-osr (⊥P) (Γ⊢δ∶x₀ ,p SNδ) δ→ε = (subject-reduction Γ⊢δ∶x₀ δ→ε) ,p (SNred SNδ (inc δ→ε))
C-osr {Γ = Γ} (φ ⇛ ψ) {δ = δ} (Γ⊢δ∶φ⇒ψ ,p Cδ) δ→δ' = subject-reduction Γ⊢δ∶φ⇒ψ δ→δ' ,p 
  (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → C-osr ψ (Cδ Q ρ ε ρ∶Γ→Δ ε∈Cφ) (app (appl (aposrr REP β-respects-rep δ→δ'))))
\end{code}
}

\begin{code}
C-red : ∀ {P} {Γ : Context P} φ {δ} {ε} → C Γ φ δ → δ ↠ ε → C Γ φ ε
\end{code}

\AgdaHide{
\begin{code}
C-red φ δ∈CΓφ (inc δ⇒ε) = C-osr φ δ∈CΓφ δ⇒ε
C-red _ δ∈CΓφ ref = δ∈CΓφ
C-red φ δ∈CΓφ (trans δ↠ε ε↠χ) = C-red φ (C-red φ δ∈CΓφ δ↠ε) ε↠χ
\end{code}
}

\item
Let $\Gamma \vdash \delta : \phi$.  
If $\delta$ is neutral and, for all $\epsilon$ such that $\delta \rightarrow_\beta \epsilon$, we have $\epsilon \in C_\Gamma(\phi)$, then $\delta \in C_\Gamma(\phi)$.
\item
If $\delta \in C_\Gamma(\phi)$ then $\delta$ is strongly normalizable.
\begin{code}
NeutralC : ∀ {P} {Γ : Context P} {δ : Proof ( P)} (φ : Prop) →
  Γ ⊢ δ ∶ φ → Neutral δ →
  (∀ ε → δ ⇒ ε → C Γ φ ε) →
  C Γ φ δ

CsubSN : ∀ {P} {Γ : Context P} φ {δ} → C Γ φ δ → SN δ
\end{code}

\AgdaHide{
\begin{code}
NeutralC {P} {Γ} {δ} {⊥P} Γ⊢δ∶x₀ Neutralδ hyp = Γ⊢δ∶x₀ ,p SNI δ (λ ε δ→ε → proj₂ (hyp ε δ→ε))
NeutralC {P} {Γ} {δ} {φ ⇛ ψ} Γ⊢δ∶φ→ψ neutralδ hyp = Γ⊢δ∶φ→ψ ,p 
  (λ Q ρ ε ρ∶Γ→Δ ε∈Cφ → claim ε (CsubSN φ {δ = ε} ε∈Cφ) ρ∶Γ→Δ ε∈Cφ) where
  claim : ∀ {Q} {Δ} {ρ : Rep P Q} ε → SN ε → ρ ∶ Γ ⇒R Δ → C Δ φ ε → C Δ ψ (appP (δ 〈  ρ 〉) ε)
  claim {Q} {Δ} {ρ} ε (SNI .ε SNε) ρ∶Γ→Δ ε∈Cφ = NeutralC {Q} {Δ} {appP (δ 〈  ρ 〉) ε} ψ
      (app 
      (weakening Γ⊢δ∶φ→ψ ρ∶Γ→Δ)
      (C-typed {Q} {Δ} {φ} {ε} ε∈Cφ)) 
      (appNeutral (δ 〈  ρ 〉) ε)
      (NeutralC-lm {X = C Δ ψ} (neutral-rep neutralδ) 
      (λ δ' δ〈ρ〉→δ' → 
        let δ-creation = create-osr β-creates-rep δ δ〈ρ〉→δ' in 
        let open creation δ-creation renaming (created to δ₀;red-created to δ⇒δ₀;ap-created to δ₀〈ρ〉≡δ') in
        let δ₀∈C[φ⇒ψ] : C Γ (φ ⇛ ψ) δ₀
            δ₀∈C[φ⇒ψ] = hyp δ₀ δ⇒δ₀
        in let δ'∈C[φ⇒ψ] : C Δ (φ ⇛ ψ) δ'
               δ'∈C[φ⇒ψ] = subst (C Δ (φ ⇛ ψ)) δ₀〈ρ〉≡δ' (C-rep (φ ⇛ ψ) δ₀∈C[φ⇒ψ] ρ∶Γ→Δ)
        in subst (C Δ ψ) (cong (λ x → appP x ε) δ₀〈ρ〉≡δ') (proj₂ δ₀∈C[φ⇒ψ] Q ρ ε ρ∶Γ→Δ ε∈Cφ))
      (λ ε' ε→ε' → claim ε' (SNε ε' ε→ε') ρ∶Γ→Δ (C-osr φ ε∈Cφ ε→ε')))

CsubSN {P} {Γ} {⊥P} = proj₂
CsubSN {P} {Γ} {φ ⇛ ψ} {δ} P₁ = 
    SNap' {REP} {P} {P , -proof} {E = δ} {σ = upRep} β-respects-rep
      (SNappl' (SNapp' (CsubSN {Γ = Γ ,P φ} ψ
      (proj₂ P₁ (P , -proof) upRep (var x₀) (↑-typed {K = -proof} {A = app (-prp φ) []})
      (NeutralC φ (var _)
        (varNeutral x₀) 
        (λ _ ()))))))
\end{code}
}

\end{enumerate}
\end{lemma}

\begin{corollary}
If $p : \phi \in \Gamma$ then $p \in C_\Gamma(\phi)$.
\end{corollary}

\begin{code}
varC : ∀ {P} {Γ : Context P} {x : Var P -proof} → 
  C Γ (unprp (typeof x Γ)) (var x)
\end{code}

\AgdaHide{
\begin{code}
varC {Γ = Γ} {x} = NeutralC (unprp (typeof x Γ)) (var x) (varNeutral x) (λ _ ())
\end{code}
}

\begin{lemma}[Computability is preserved under well-typed expansion]
Suppose $\Gamma, p : \phi \vdash \delta : \psi$ and $\Gamma \vdash \epsilon : \phi$.  If
$\delta[p:=\epsilon] \in C_\Gamma(\psi)$ and $\epsilon \in SN$, then $(\lambda p:\phi.\delta)\epsilon \in C_\Gamma(\psi)$.
\end{lemma}

\AgdaHide{
\begin{code}
WTEaux : ∀ {P} {Γ : Context P} {φ} {δ} ψ {ε} →
  Γ ,P φ ⊢ δ ∶ ψ →
  Γ ⊢ ε ∶ φ →
  C Γ ψ (δ ⟦ x₀:= ε ⟧) →
  SN δ → SN ε →
  C Γ ψ (appP (ΛP φ δ) ε)
WTEaux {Γ = Γ} {φ = φ} ψ Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ (SNI δ SNδ) (SNI ε SNε) = NeutralC {Γ = Γ} {δ = appP (ΛP φ δ) ε} ψ
  (app (Λ Γ,p∶φ⊢δ∶ψ) Γ⊢ε∶φ) 
  (appNeutral _ _) 
  (λ χ Λφδε⇒χ → red-β-redex (C Γ ψ) Λφδε⇒χ δ[p∶=ε]∈CΓψ
    (λ δ' δ⇒δ' → WTEaux ψ
      (subject-reduction Γ,p∶φ⊢δ∶ψ δ⇒δ') 
      Γ⊢ε∶φ 
      (C-osr ψ δ[p∶=ε]∈CΓψ (aposrr SUB β-respects-sub δ⇒δ')) 
      (SNδ δ' δ⇒δ') (SNI ε SNε)) 
    (λ ε' ε⇒ε' → WTEaux ψ
    Γ,p∶φ⊢δ∶ψ 
    (subject-reduction Γ⊢ε∶φ ε⇒ε') 
    (C-red ψ {δ ⟦ x₀:= ε ⟧} {δ ⟦ x₀:= ε' ⟧} δ[p∶=ε]∈CΓψ (apredl SUB {E = δ} β-respects-sub (botsub-red ε⇒ε'))) 
    (SNI δ SNδ) (SNε _ ε⇒ε')))
\end{code}
}

\begin{code}
WTE : ∀ {P} {Γ : Context P} {φ} {δ} {ψ} {ε} →
  Γ ,P φ ⊢ δ ∶ ψ →
  Γ ⊢ ε ∶ φ →
  C Γ ψ (δ ⟦ x₀:= ε ⟧) →
  SN ε →
  C Γ ψ (appP (ΛP φ δ) ε)
\end{code}

\AgdaHide{
\begin{code}
WTE {ψ = ψ} Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ = WTEaux ψ Γ,p∶φ⊢δ∶ψ Γ⊢ε∶φ δ[p∶=ε]∈CΓψ (SNap' {SUB} β-respects-sub (CsubSN ψ δ[p∶=ε]∈CΓψ))
\end{code}
}

\begin{lm}
If $\delta \in C_\Gamma(\phi \rightarrow \psi)$ and $\epsilon \in C_\Gamma(\phi)$ then $\delta \epsilon \in C_\Gamma(\psi)$.
\end{lm}

\begin{code}
C-app : ∀ {P} {Γ : Context P} {δ ε φ ψ} → C Γ (φ ⇛ ψ) δ → C Γ φ ε → C Γ ψ (appP δ ε)
C-app {P} {Γ} {δ} {ε} {φ} {ψ} (Γ⊢δ∶φ⇛ψ ,p δ∈CΓφ⇛ψ) ε∈CΓφ =
  subst (λ x → C Γ ψ (appP x ε)) rep-idRep (δ∈CΓφ⇛ψ P (idRep P) ε idRep-typed ε∈CΓφ)
\end{code}

A substitution $\sigma$ is a \emph{computable} substitution from $\Gamma$ to $\Delta$, $\sigma : \Gamma \rightarrow_C \Delta$,
iff for all $p : \phi \in \Gamma$ we have $\sigma(p) \in C_\Delta(\phi)$.

\begin{code}
_∶_⇒C_ : ∀ {P} {Q} → Sub P Q → Context P → Context Q → Set
σ ∶ Γ ⇒C Δ = ∀ x → C Δ (unprp (typeof {K = -proof} x Γ)) (σ _ x)
\end{code}

\begin{prop}
If $\sigma : \Gamma \rightarrow_C \Delta$ then $\sigma : \Gamma \rightarrow \Delta$.
\end{prop}

\begin{code}
SubC-typed : ∀ {P Q} {σ : Sub P Q} {Γ Δ} → σ ∶ Γ ⇒C Δ → σ ∶ Γ ⇒ Δ
SubC-typed σ∶Γ⇒CΔ x = C-typed (σ∶Γ⇒CΔ x)
\end{code}

\begin{prop}
If $\Gamma \vdash \delta : \phi$ and $\sigma : \Gamma \rightarrow_C \Delta$ then $\delta [ \sigma ] \in C_\Delta(\phi)$.
\end{prop}

\begin{code}
compRSC : ∀ {P} {Q} {R}
  {ρ : Rep Q R} {σ : Sub P Q}
  {Γ : Context P} {Δ : Context Q} {Θ : Context R} →
  ρ ∶ Δ ⇒R Θ → σ ∶ Γ ⇒C Δ → ρ •RS σ ∶ Γ ⇒C Θ
compRSC {Γ = Γ} ρ∶Δ⇒RΘ σ∶Γ⇒CΔ x = 
      C-rep (unprp (typeof x Γ)) (σ∶Γ⇒CΔ x) ρ∶Δ⇒RΘ

extend-sub : ∀ {P} {Q} {σ : Sub P Q} {Γ} {Δ} {δ} {φ} →
           σ ∶ Γ ⇒C Δ → C Δ φ δ → x₀:= δ • liftSub _ σ ∶ Γ ,P φ ⇒C Δ
extend-sub σ∶Γ⇒CΔ δ∈CΔφ x₀ = δ∈CΔφ
extend-sub {σ = σ} {Γ} {Δ = Δ} {δ} {φ} σ∶Γ⇒CΔ δ∈CΔφ (↑ x) =
  let σx∈CΔφ : C Δ (unprp (typeof x Γ)) (σ _ x)
      σx∈CΔφ = σ∶Γ⇒CΔ x in
  subst₂ (C Δ) 
  (let open ≡-Reasoning in
  begin
    unprp (typeof x Γ)
  ≡⟨⟨ unprp-rep (typeof x Γ) upRep ⟩⟩
    unprp (typeof x Γ ⇑)
  ∎) (let open ≡-Reasoning in
  begin
    σ _ x
  ≡⟨⟨ botSub-upRep (σ _ x) ⟩⟩
    σ _ x ⇑ ⟦ x₀:= δ ⟧
  ∎) σx∈CΔφ

SNmainlemma : ∀ {P} {Q} {Γ : Context P} {δ} {φ} {σ : Sub P Q} {Δ} →
  Γ ⊢ δ ∶ φ → σ ∶ Γ ⇒C Δ →
  C Δ φ (δ ⟦ σ ⟧)
\end{code}

\AgdaHide{
\begin{code}
SNmainlemma (var p) σ∶Γ⇒CΔ = σ∶Γ⇒CΔ p
SNmainlemma (app Γ⊢δ∶φ⇛ψ Γ⊢ε∶φ) σ∶Γ⇒CΔ = 
  C-app (SNmainlemma Γ⊢δ∶φ⇛ψ σ∶Γ⇒CΔ) (SNmainlemma Γ⊢ε∶φ σ∶Γ⇒CΔ)
SNmainlemma {P} {Γ = Γ} {σ = σ} {Δ} (Λ {φ = φ} {δ = δ} {ψ} Γ,φ⊢δ∶ψ) σ∶Γ⇒CΔ = (substitution (Λ Γ,φ⊢δ∶ψ) (SubC-typed {σ = σ} σ∶Γ⇒CΔ)) ,p 
  (λ R {Θ} ρ ε ρ∶Δ⇒RΘ ε∈CΘφ → 
    let δσ[ε]∈CΘψ : C Θ ψ (δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧)
        δσ[ε]∈CΘψ = subst (C Θ ψ) 
          (let open ≡-Reasoning in
            δ ⟦ x₀:= ε • liftSub _ (ρ •RS σ) ⟧
          ≡⟨ sub-comp δ ⟩
            δ ⟦ liftSub _ (ρ •RS σ) ⟧ ⟦ x₀:= ε ⟧
          ≡⟨ sub-congl (sub-congr δ liftSub-compRS) ⟩
            δ ⟦ liftRep _ ρ •RS liftSub _ σ ⟧ ⟦ x₀:= ε ⟧
          ≡⟨ sub-congl (sub-compRS δ) ⟩
            δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉 ⟦ x₀:= ε ⟧
          ∎) 
          (SNmainlemma Γ,φ⊢δ∶ψ (extend-sub (compRSC {σ = σ} ρ∶Δ⇒RΘ σ∶Γ⇒CΔ) ε∈CΘφ)) in
        WTE {R} {Θ} {φ} {δ ⟦ liftSub _ σ ⟧ 〈 liftRep _ ρ 〉} {ψ} {ε}
        (weakening (substitution Γ,φ⊢δ∶ψ (liftSub-typed (SubC-typed {σ = σ} {Γ} {Δ} σ∶Γ⇒CΔ))) (liftRep-typed ρ∶Δ⇒RΘ)) 
        (C-typed ε∈CΘφ) 
        δσ[ε]∈CΘψ 
        (CsubSN φ ε∈CΘφ))
\end{code}
}

\begin{theorem}
Propositional Logic is strongly normalizing.
\end{theorem}

\begin{code}
Strong-Normalization : ∀ {P} {Γ : Context P} {δ} {φ} → Γ ⊢ δ ∶ φ → SN δ
\end{code}

\AgdaHide{
\begin{code}
Strong-Normalization {P} {Γ} {δ} {φ} Γ⊢δ:φ = subst SN 
  sub-idSub
  (CsubSN (φ) {δ ⟦ idSub P ⟧}
  (SNmainlemma Γ⊢δ:φ (λ x → varC {x = x})))
\end{code}
}
