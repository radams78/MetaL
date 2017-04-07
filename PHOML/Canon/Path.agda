module PHOML.Canon.Path where
open import Data.Sum
open import Data.Product renaming (_,_ to _,p_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Neutral
open import PHOML.Red

-- Canonical paths of equations φ ≡〈 Ω 〉 ψ
data CanonΩ (V : Alphabet) : Set where
  neutral : NeutralE V → CanonΩ V
  reffC   : Term V → CanonΩ V
  univC   : Term V → Term V → Proof V → Proof V → CanonΩ V

decode-CanonΩ : ∀ {V} → CanonΩ V → Path V
decode-CanonΩ (neutral P) = decode-NeutralE P
decode-CanonΩ (reffC M) = reff M
decode-CanonΩ (univC φ ψ δ ε) = univ φ ψ δ ε

reflect-canonΩ : ∀ {U V} {P : Path U} {Q : CanonΩ V} {ρ : Rep U V} →
  P 〈 ρ 〉 ≡ decode-CanonΩ Q → Σ[ P' ∈ CanonΩ U ] P ≡ decode-CanonΩ P'
reflect-canonΩ {P = P} {neutral Q} {ρ} Pρ≡Q = 
  let P' ,p P≡P' = reflect-NeutralE P Q ρ Pρ≡Q in
  neutral P' ,p P≡P'
reflect-canonΩ {P = var _} {reffC _} ()
reflect-canonΩ {P = app -ref (M ∷ [])} {reffC N} Pρ≡refM = 
  (reffC M) ,p refl
reflect-canonΩ {P = app -imp* x₁} {reffC M} ()
reflect-canonΩ {P = app -univ x₁} {reffC M} ()
reflect-canonΩ {P = app (-lll x) x₁} {reffC M} ()
reflect-canonΩ {P = app -app* x₁} {reffC M} ()
reflect-canonΩ {P = var x} {univC x₁ x₂ x₃ x₄} ()
reflect-canonΩ {P = app -ref x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonΩ {P = app -imp* x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonΩ {P = app -univ (M₁ ∷ (M₂ ∷ (δ₁ ∷ (δ₂ ∷ []))))} {univC N₁ N₂ Q₁ Q₂} Pρ≡Q = univC M₁ M₂ δ₁ δ₂ ,p refl
reflect-canonΩ {P = app (-lll x) x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonΩ {P = app -app* x₁} {univC x₂ x₃ x₄ x₅} ()

data CanonE (V : Alphabet) : Set where
  neutral : NeutralE V → CanonE V
  reffC   : Term V → CanonE V
  univC   : Term V → Term V → Proof V → Proof V → CanonE V
  λλλC    : Type → Path (extend V pathDom) → CanonE V

decode-CanonE : ∀ {V} → CanonE V → Path V
decode-CanonE (neutral P) = decode-NeutralE P
decode-CanonE (reffC M) = reff M
decode-CanonE (univC φ ψ δ ε) = univ φ ψ δ ε
decode-CanonE (λλλC A P) = λλλ A P

app*-CanonE : ∀ {V} {P Q : Path V} {M N P₀} → app* M N P Q ≡ decode-CanonE P₀ → Σ[ N ∈ NeutralE V ] P ≡ decode-NeutralE N
app*-CanonE {P₀ = neutral (var _)} ()
app*-CanonE {P₀ = neutral (app*N _ _ P _)} PQ≡PQ = P ,p app*-injl PQ≡PQ
app*-CanonE {P₀ = neutral (imp*l _ _)} ()
app*-CanonE {P₀ = neutral (imp*r _ _)} ()
app*-CanonE {P₀ = reffC _} ()
app*-CanonE {P₀ = univC _ _ _ _} ()
app*-CanonE {P₀ = λλλC _ _} ()

reflect-canonE : ∀ {U V} {P : Path U} {Q : CanonE V} {ρ : Rep U V} →
  P 〈 ρ 〉 ≡ decode-CanonE Q → Σ[ P' ∈ CanonE U ] P ≡ decode-CanonE P'
reflect-canonE {P = P} {neutral Q} {ρ} Pρ≡Q = 
  let P' ,p P≡P' = reflect-NeutralE P Q ρ Pρ≡Q in
  neutral P' ,p P≡P'
reflect-canonE {P = var _} {reffC _} ()
reflect-canonE {P = app -ref (M ∷ [])} {reffC N} Pρ≡refM = 
  (reffC M) ,p refl
reflect-canonE {P = app -imp* x₁} {reffC M} ()
reflect-canonE {P = app -univ x₁} {reffC M} ()
reflect-canonE {P = app (-lll x) x₁} {reffC M} ()
reflect-canonE {P = app -app* x₁} {reffC M} ()
reflect-canonE {P = var x} {univC x₁ x₂ x₃ x₄} ()
reflect-canonE {P = app -ref x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = app -imp* x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = app -univ (M₁ ∷ (M₂ ∷ (δ₁ ∷ (δ₂ ∷ []))))} {univC N₁ N₂ Q₁ Q₂} Pρ≡Q = univC M₁ M₂ δ₁ δ₂ ,p refl
reflect-canonE {P = app (-lll x) x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = app -app* x₁} {univC x₂ x₃ x₄ x₅} ()
reflect-canonE {P = var _} {λλλC _ _} ()
reflect-canonE {P = app -ref _} {λλλC _ _} ()
reflect-canonE {P = app -imp* _} {λλλC _ _} ()
reflect-canonE {P = app -univ _} {λλλC _ _} ()
reflect-canonE {P = app (-lll A') (Q' ∷ [])} {λλλC A Q} Pρ≡lllQ = (λλλC A' Q' ) ,p refl
reflect-canonE {P = app -app* _} {λλλC _ _} ()

CanonΩ2CanonE : ∀ {V} → CanonΩ V → CanonE V
CanonΩ2CanonE (neutral N) = neutral N
CanonΩ2CanonE (reffC M) = reffC M
CanonΩ2CanonE (univC M N P Q) = univC M N P Q

decode-CanonΩE : ∀ {V} {P : CanonΩ V} → decode-CanonΩ P ≡ decode-CanonE (CanonΩ2CanonE P)
decode-CanonΩE {P = neutral _} = refl
decode-CanonΩE {P = reffC _} = refl
decode-CanonΩE {P = univC _ _ _ _} = refl

Lemma35a : ∀ {V} {P : Path V} {pp : snocList (Var V -Proof)} {δ d} →
  APPP (dir d P) (snocmap var pp) ⇒ δ →
  Σ[ Q ∈ Path V ] (P ⇒ Q × δ ≡ APPP (dir d Q) (snocmap var pp)) ⊎
  Σ[ Q ∈ CanonΩ V ] P ≡ decode-CanonΩ Q
Lemma35a {pp = []} refdir = inj₂ ((reffC _) ,p refl)
Lemma35a {pp = []} univplus = inj₂ ((univC _ _ _ _) ,p refl)
Lemma35a {pp = []} univminus = inj₂ ((univC _ _ _ _) ,p refl)
Lemma35a {pp = [] snoc p} (appPl univplus) = inj₂ ((univC _ _ _ _) ,p refl)
Lemma35a {pp = [] snoc p} (appPl univminus) = inj₂ ((univC _ _ _ _) ,p refl)
Lemma35a {pp = [] snoc _} (appPl refdir) = inj₂ (reffC _ ,p refl)
Lemma35a {pp = (pp snoc x) snoc _} (appPl Pppx⇒δ) with Lemma35a {pp = pp snoc x} Pppx⇒δ
Lemma35a {pp = (_ snoc _) snoc y} (appPl _) | inj₁ (Q ,p P⇒Q ,p δ≡Qppx) = inj₁ (Q ,p P⇒Q ,p cong (λ z → appP z (var y)) δ≡Qppx)
Lemma35a {pp = (_ snoc _) snoc _} (appPl _) | inj₂ Pcanon = inj₂ Pcanon
Lemma35a {pp = []} (dirR P⇒P') = inj₁ (_ ,p P⇒P' ,p refl)
Lemma35a {pp = [] snoc p} (appPl (dirR P⇒P')) = inj₁ (_ ,p P⇒P' ,p refl)

Lemma35b : ∀ {V} {P : Path V} (pp : snocList (Var V -Proof)) {α β d} →
  α ↠ β → α ≡ APPP (dir d P) (snocmap var pp) →
  Σ[ Q ∈ Path V ] (P ↠ Q × β ≡ APPP (dir d Q) (snocmap var pp)) ⊎
  Σ[ Q ∈ CanonΩ V ] P ↠ decode-CanonΩ Q
Lemma35b pp {β = β} (inc α⇒β) α≡Ppp with Lemma35a {pp = pp} (subst (λ x → x ⇒ β) α≡Ppp α⇒β) 
Lemma35b _ (inc α⇒β) α≡Ppp | inj₁ (Q ,p P⇒Q ,p β≡Q+pp) = inj₁ (Q ,p inc P⇒Q ,p β≡Q+pp)
Lemma35b {P = P} _ (inc α⇒β) α≡Ppp | inj₂ (Q ,p P≡Q) = inj₂ (Q ,p subst (λ x → P ↠ x) P≡Q ref)
Lemma35b {P = P} _ ref β≡Ppp = inj₁ (P ,p ref ,p β≡Ppp)
Lemma35b pp (trans α↠β β↠γ) α≡P+pp with Lemma35b pp α↠β α≡P+pp
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₁ (Q ,p P↠Q ,p β≡Q+pp) with Lemma35b pp β↠γ β≡Q+pp
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₁ (Q ,p P↠Q ,p β≡Q+pp) | inj₁ (R ,p Q↠R ,p γ≡R+pp) = inj₁ (R ,p trans P↠Q Q↠R ,p γ≡R+pp)
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₁ (Q ,p P↠Q ,p β≡Q+pp) | inj₂ (R ,p Q↠R) = inj₂ (R ,p (trans P↠Q Q↠R))
Lemma35b pp (trans α↠β β↠γ) α≡P+pp | inj₂ Predcanon = inj₂ Predcanon

Lemma35c : ∀ {V} {P : Path V} (pp : snocList (Var V -Proof)) (δ : NeutralP V) {d} →
  APPP (dir d P) (snocmap var pp) ↠ decode-NeutralP δ →
  Σ[ Q ∈ CanonΩ V ] P ↠ decode-CanonΩ Q
Lemma35c pp _ P+pp↠δ with Lemma35b pp P+pp↠δ refl
Lemma35c [] (var _) _ | inj₁ (_ ,p _ ,p ())
Lemma35c (pp snoc p) (var q) P+pp↠q | inj₁ (_ ,p _ ,p ())
Lemma35c [] (app _ _) _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (dirN -plus R) {d = -plus} _ | inj₁ (_ ,p P↠Q ,p R+≡Q+) = (neutral R) ,p (subst (λ x → P ↠ x) (≡-sym (dir-inj R+≡Q+)) P↠Q)
Lemma35c {P = P} [] (dirN -plus R) {d = -minus} _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (dirN -minus R) {d = -plus} _ | inj₁ (_ ,p _ ,p ())
Lemma35c {P = P} [] (dirN -minus R) {d = -minus} _ | inj₁ (_ ,p P↠Q ,p R+≡Q+) = (neutral R) ,p (subst (λ x → P ↠ x) (≡-sym (dir-inj R+≡Q+)) P↠Q)
Lemma35c {P = P} (pp snoc p) (app δ x) {d} P+pp↠δ | inj₁ (Q ,p P↠Q ,p Q+pp≡δ) = 
  Lemma35c pp δ (subst (λ x₃ → APPP (dir d P) (snocmap var pp) ↠ x₃) (≡-sym (appP-injl Q+pp≡δ)) (↠-APPP (snocmap var pp) (↠-dir P↠Q)))
Lemma35c (pp snoc p) (dirN _ x) P+pp↠δ | inj₁ (Q ,p P↠Q ,p ())
Lemma35c _ _ P+pp↠δ | inj₂ Pcanon = Pcanon

red-app*l : ∀ {V} {M N : Term V} {P P' Q₁ Q₂ : Path V} → P ↠ P' → P ≡ app* M N Q₁ Q₂ →
  Σ[ Q₁' ∈ Path V ] (Q₁ ↠ Q₁' × P' ≡ app* M N Q₁' Q₂) ⊎
  Σ[ R ∈ CanonE V ] Q₁ ↠ decode-CanonE R
red-app*l {Q₁ = Q₁} (inc (βE {A = A} {P = P})) P≡Q₁Q₂ = inj₂ (λλλC A P ,p subst (λ x → Q₁ ↠ x) (≡-sym (app*-injl P≡Q₁Q₂)) ref)
red-app*l {Q₁ = Q₁} (inc (βPP {A = A} {M = M})) P≡Q₁Q₂ = inj₂ (reffC (ΛT A M) ,p subst (λ x → Q₁ ↠ x) (≡-sym (app*-injl P≡Q₁Q₂)) ref)
red-app*l (inc ref⊃*) ()
red-app*l (inc ref⊃*univ) ()
red-app*l (inc univ⊃*ref) ()
red-app*l (inc univ⊃*univ) ()
red-app*l (inc (imp*l _)) ()
red-app*l (inc (imp*r _)) ()
red-app*l {M = M} {N} {Q₁ = Q₁} {Q₂} (inc (app*l {P' = P'} P⇒P')) P≡Q₁Q₂ = inj₁ (P' ,p (subst (λ x → x ↠ P') (app*-injl P≡Q₁Q₂) (inc P⇒P')) ,p 
  cong₄ app* (app*-inj₁ P≡Q₁Q₂) (app*-inj₂ P≡Q₁Q₂) refl (app*-injr P≡Q₁Q₂))
red-app*l (inc (reffR {M = M} M⇒M')) refMQ≡refMQ = inj₂ (reffC M ,p subst (λ x → x ↠ reff M) (app*-injl refMQ≡refMQ) ref)
red-app*l ref P≡Q₁Q₂ = inj₁ (_ ,p ref ,p P≡Q₁Q₂)
red-app*l (trans P↠P' P'↠P'') P≡Q₁Q₂ with red-app*l P↠P' P≡Q₁Q₂
red-app*l (trans P↠P' P'↠P'') P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p P'≡Q₁'Q₂) with red-app*l P'↠P'' P'≡Q₁'Q₂
red-app*l (trans P↠P' P'↠P'') P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p P'≡Q₁'Q₂) | inj₁ (Q₁'' ,p Q₁'↠Q₁'' ,p P''≡Q₁''Q₂) = inj₁ (Q₁'' ,p trans Q₁↠Q₁' Q₁'↠Q₁'' ,p P''≡Q₁''Q₂)
red-app*l (trans P↠P' P'↠P'') P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p P'≡Q₁'Q₂) | inj₂ (Q₁'' ,p Q₁'↠Q₁'') = inj₂ (Q₁'' ,p (trans Q₁↠Q₁' Q₁'↠Q₁''))
red-app*l (trans P↠P' P'↠P'') P≡Q₁Q₂ | inj₂ Pcanon = inj₂ Pcanon

app*-wnl : ∀ {V} {M N : Term V} {P Q₁ Q₂ : Path V} {R} → P ↠ decode-CanonE R → P ≡ app* M N Q₁ Q₂ → Σ[ R' ∈ CanonE V ] Q₁ ↠ decode-CanonE R'
app*-wnl P↠R P≡Q₁Q₂ with red-app*l P↠R P≡Q₁Q₂
app*-wnl {R = neutral (var x)} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p ())
app*-wnl {Q₁ = Q₁} {R = neutral (app*N x x₁ Q₀ x₃)} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p P'≡Q₁'Q₂) = (neutral Q₀) ,p 
  (subst (λ x₄ → Q₁ ↠ x₄) (≡-sym (app*-injl P'≡Q₁'Q₂)) Q₁↠Q₁')
app*-wnl {R = neutral (imp*l x x₁)} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p ())
app*-wnl {R = neutral (imp*r x x₁)} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p ())
app*-wnl {R = reffC x} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p ())
app*-wnl {R = univC x x₁ x₂ x₃} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p ())
app*-wnl {R = λλλC x x₁} P↠R P≡Q₁Q₂ | inj₁ (Q₁' ,p Q₁↠Q₁' ,p ())
app*-wnl P↠R P≡Q₁Q₂ | inj₂ Q₁canon = Q₁canon

