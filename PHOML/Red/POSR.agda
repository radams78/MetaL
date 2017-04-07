--Parallel one-step reduction
module PHOML.Red.POSR where
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RTRed

data _▷_ : ∀ {V K} → VExpression V K → VExpression V K → Set where
  ref : ∀ {V K} {E : VExpression V K} → E ▷ E
  βT : ∀ {V A M} {N : Term V} → appT (ΛT A M) N ▷ M ⟦ x₀:= N ⟧
  appTl : ∀ {V} {M M' N : Term V} → M ▷ M' → appT M N ▷ appT M' N
  imp : ∀ {V} {φ φ' ψ ψ' : Term V} → φ ▷ φ' → ψ ▷ ψ' → φ ⊃ ψ ▷ φ' ⊃ ψ'
  βP : ∀ {V} {φ : Term V} {δ ε} → appP (ΛP φ δ) ε ▷ δ ⟦ x₀:= ε ⟧
  refdir : ∀ {V} {φ : Term V} {d} → dir d (reff φ) ▷ ΛP φ (var x₀)
  appPl : ∀ {V} {δ δ' ε : Proof V} → δ ▷ δ' → appP δ ε ▷ appP δ' ε
  univplus : ∀ {V} {φ ψ : Term V} {δ ε} → plus (univ φ ψ δ ε) ▷ δ
  univminus : ∀ {V} {φ ψ : Term V} {δ ε} → minus (univ φ ψ δ ε) ▷ ε
  dirR : ∀ {V} {P Q : Path V} {d} → P ▷ Q → dir d P ▷ dir d Q
  βE : ∀ {V} {M N : Term V} {A P Q} → app* M N (λλλ A P) Q ▷ P ⟦ x₂:= M ,x₁:= N ,x₀:= Q ⟧
  βPP : ∀ {V} {N N' : Term V} {A M P} → app* N N' (reff (ΛT A M)) P ▷ M ⟦⟦ x₀::= P ∶ x₀:= N ≡ x₀:= N' ⟧⟧
  ref⊃*ref : ∀ {V} {φ ψ : Term V} → (reff φ ⊃* reff ψ) ▷ reff (φ ⊃ ψ)
  ref⊃*univ : ∀ {V} {φ ψ χ : Term V} {δ ε} → 
    (reff φ ⊃* univ ψ χ δ ε) ▷ univ (φ ⊃ ψ) (φ ⊃ χ) (ΛP (φ ⊃ ψ) (ΛP (φ ⇑) (appP (δ ⇑ ⇑) (appP (var x₁) (var x₀))))) (ΛP (φ ⊃ χ) (ΛP (φ ⇑) (appP (ε ⇑ ⇑) (appP (var x₁) (var x₀)))))
  univ⊃*ref : ∀ {V} {φ ψ χ : Term V} {δ ε} →
    (univ φ ψ δ ε ⊃* reff χ) ▷ univ (φ ⊃ χ) (ψ ⊃ χ) (ΛP (φ ⊃ χ) (ΛP (ψ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀))))) (ΛP (ψ ⊃ χ) (ΛP (φ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀)))))
  univ⊃*univ : ∀ {V} {φ φ' ψ ψ' : Term V} {δ δ' ε ε'} →
    (univ φ ψ δ ε ⊃* univ φ' ψ' δ' ε') ▷ univ (φ ⊃ φ') (ψ ⊃ ψ') (ΛP (φ ⊃ φ') (ΛP (ψ ⇑) (appP (δ' ⇑ ⇑) (appP (var x₁) (appP (ε ⇑ ⇑) (var x₀)))))) (ΛP (ψ ⊃ ψ') (ΛP (φ ⇑) (appP (ε' ⇑ ⇑) (appP (var x₁) (appP (δ ⇑ ⇑) (var x₀))))))
  app*l : ∀ {V M N} {P P' Q : Path V} → P ▷ P' → app* M N P Q ▷ app* M N P' Q
  ⊃* : ∀ {V} {P P' Q Q' : Path V} → P ▷ P' → Q ▷ Q' → (P ⊃* Q) ▷ (P' ⊃* Q')
  reffR : ∀ {V} {M M' N N' : Term V} {P} → M ▷ M' → app* N N' (reff M) P ▷ app* N N' (reff M') P

sub-⇒-▷ : ∀ {V K} {E F : VExpression V K} → E ⇒ F → E ▷ F
sub-⇒-▷ βT = βT
sub-⇒-▷ (appTl E⇒F) = appTl (sub-⇒-▷ E⇒F)
sub-⇒-▷ (impl E⇒F) = imp (sub-⇒-▷ E⇒F) ref
sub-⇒-▷ (impr E⇒F) = imp ref (sub-⇒-▷ E⇒F)
sub-⇒-▷ βP = βP
sub-⇒-▷ refdir = refdir
sub-⇒-▷ (appPl E⇒F) = appPl (sub-⇒-▷ E⇒F)
sub-⇒-▷ univplus = univplus
sub-⇒-▷ univminus = univminus
sub-⇒-▷ βE = βE
sub-⇒-▷ βPP = βPP
sub-⇒-▷ ref⊃* = ref⊃*ref
sub-⇒-▷ ref⊃*univ = ref⊃*univ
sub-⇒-▷ univ⊃*ref = univ⊃*ref
sub-⇒-▷ univ⊃*univ = univ⊃*univ
sub-⇒-▷ (app*l E⇒F) = app*l (sub-⇒-▷ E⇒F)
sub-⇒-▷ (imp*l E⇒F) = ⊃* (sub-⇒-▷ E⇒F) ref
sub-⇒-▷ (imp*r E⇒F) = ⊃* ref (sub-⇒-▷ E⇒F)
sub-⇒-▷ (reffR M⇒M') = reffR (sub-⇒-▷ M⇒M')
sub-⇒-▷ (dirR P⇒Q) = dirR (sub-⇒-▷ P⇒Q)

sub-▷-↠ : ∀ {V K} {E F : VExpression V K} → E ▷ F → E ↠ F
sub-▷-↠ ref = ref
sub-▷-↠ βT = inc βT
sub-▷-↠ (appTl E▷F) = ↠-appT (sub-▷-↠ E▷F)
sub-▷-↠ (imp φ▷φ' ψ▷ψ') = ↠-imp (sub-▷-↠ φ▷φ') (sub-▷-↠ ψ▷ψ')
sub-▷-↠ βP = inc βP
sub-▷-↠ refdir = inc refdir
sub-▷-↠ (appPl E▷F) = ↠-appP (sub-▷-↠ E▷F)
sub-▷-↠ univplus = inc univplus
sub-▷-↠ univminus = inc univminus
sub-▷-↠ βE = inc βE
sub-▷-↠ βPP = inc βPP
sub-▷-↠ ref⊃*ref = inc ref⊃*
sub-▷-↠ ref⊃*univ = inc ref⊃*univ
sub-▷-↠ univ⊃*ref = inc univ⊃*ref
sub-▷-↠ univ⊃*univ = inc univ⊃*univ
sub-▷-↠ (app*l E▷F) = ↠-app*l (sub-▷-↠ E▷F)
sub-▷-↠ (⊃* P▷P' Q▷Q') = ↠-imp* (sub-▷-↠ P▷P') (sub-▷-↠ Q▷Q')
sub-▷-↠ (reffR M▷M') = ↠-app*ref (sub-▷-↠ M▷M')
sub-▷-↠ (dirR P▷Q) = ↠-dir (sub-▷-↠ P▷Q)

diamond-▷ : ∀ {V K} {E F G : VExpression V K} → E ▷ F → E ▷ G → Common-Reduct _▷_ _▷_ F G
diamond-▷ {G = G} ref E▷G = cr G E▷G ref
diamond-▷ {G = G} (appTl ref) E▷G = cr G E▷G ref
diamond-▷ {G = G} (appPl ref) E▷G = cr G E▷G ref
diamond-▷ {G = G} (app*l ref) E▷G = cr G E▷G ref
diamond-▷ {G = G} (reffR ref) E▷G = cr G E▷G ref
diamond-▷ {G = G} (⊃* ref ref) E▷G = cr G E▷G ref
diamond-▷ {G = G} (dirR ref) E▷G = cr G E▷G ref
diamond-▷ {F = F} E▷F ref = cr F ref E▷F
diamond-▷ {F = F} E▷F (appTl ref) = cr F ref E▷F
diamond-▷ {F = F} E▷F (appPl ref) = cr F ref E▷F
diamond-▷ {F = F} E▷F (app*l ref) = cr F ref E▷F
diamond-▷ {F = F} E▷F (⊃* ref ref) = cr F ref E▷F
diamond-▷ {F = F} E▷F (reffR ref) = cr F ref E▷F
diamond-▷ {F = F} E▷F (dirR ref) = cr F ref E▷F
diamond-▷ βT βT = cr _ ref ref
diamond-▷ (appTl M▷M') (appTl M▷M'') = let cr M₀ M'▷M₀ M''▷M₀ = diamond-▷ M▷M' M▷M'' in cr (appT M₀ _) (appTl M'▷M₀) (appTl M''▷M₀)
diamond-▷ (imp φ▷φ' ψ▷ψ') (imp φ▷φ'' ψ▷ψ'') =
  let cr φ₀ φ'▷φ₀ φ''▷φ₀ = diamond-▷ φ▷φ' φ▷φ'' in 
  let cr ψ₀ ψ'▷ψ₀ ψ''▷ψ₀ = diamond-▷ ψ▷ψ' ψ▷ψ'' in 
  cr (φ₀ ⊃ ψ₀) (imp φ'▷φ₀ ψ'▷ψ₀) (imp φ''▷φ₀ ψ''▷ψ₀)
diamond-▷ βP βP = cr _ ref ref
diamond-▷ refdir refdir = cr _ ref ref
diamond-▷ (appPl δ▷δ') (appPl δ▷δ'') = let cr δ₀ δ'▷δ₀ δ''▷δ₀ = diamond-▷ δ▷δ' δ▷δ'' in cr _ (appPl δ'▷δ₀) (appPl δ''▷δ₀)
diamond-▷ univplus univplus = cr _ ref ref
diamond-▷ univminus univminus = cr _ ref ref
diamond-▷ βE βE = cr _ ref ref
diamond-▷ βPP βPP = cr _ ref ref
diamond-▷ ref⊃*ref ref⊃*ref = cr _ ref ref
diamond-▷ ref⊃*univ ref⊃*univ = cr _ ref ref
diamond-▷ univ⊃*ref univ⊃*ref = cr _ ref ref
diamond-▷ univ⊃*univ univ⊃*univ = cr _ ref ref
diamond-▷ (app*l P▷P') (app*l P▷P'') = let cr P₀ P'▷P₀ P''▷P₀ = diamond-▷ P▷P' P▷P'' in 
  cr _ (app*l P'▷P₀) (app*l P''▷P₀)
diamond-▷ (reffR M▷M') (reffR M▷M'') = let cr M₀ M'▷M₀ M''▷M₀ = diamond-▷ M▷M' M▷M'' in 
  cr _ (reffR M'▷M₀) (reffR M''▷M₀)
diamond-▷ (⊃* P▷P' Q▷Q') (⊃* P▷P'' Q▷Q'') =
  let cr P₀ P'▷P₀ P''▷P₀ = diamond-▷ P▷P' P▷P'' in
  let cr Q₀ Q'▷Q₀ Q''▷Q₀ = diamond-▷ Q▷Q' Q▷Q'' in
  cr _ (⊃* P'▷P₀ Q'▷Q₀) (⊃* P''▷P₀ Q''▷Q₀)
diamond-▷ (dirR P▷Q) (dirR P▷R) = 
  let cr P₀ Q▷P₀ R▷P₀ = diamond-▷ P▷Q P▷R in
  cr (dir _ P₀) (dirR Q▷P₀) (dirR R▷P₀)
