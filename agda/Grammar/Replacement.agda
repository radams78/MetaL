--Variable convention: ρ ranges over replacements
open import Grammar.Base

module Grammar.Replacement (G : Grammar) where

open import Function
open import Prelims
open Grammar G
open import Grammar.OpFamily.PreOpFamily G
open import Grammar.OpFamily.LiftFamily G
open import Grammar.OpFamily.OpFamily G

Rep : Alphabet → Alphabet → Set
Rep U V = ∀ K → Var U K → Var V K

upRep : ∀ {V} {K} → Rep V (V , K)
upRep _ = ↑

idRep : ∀ V → Rep V V
idRep _ _ x = x

Rep∶POF : PreOpFamily
Rep∶POF = record { 
  Op = Rep; 
  apV = λ ρ x → var (ρ _ x); 
  up = upRep; 
  apV-up = refl; 
  idOp = idRep; 
  apV-idOp = λ _ → refl }

_∼R_ : ∀ {U} {V} → Rep U V → Rep U V → Set
_∼R_ = PreOpFamily._∼op_ Rep∶POF

liftRep : ∀ {U} {V} K → Rep U V → Rep (U , K) (V , K)
liftRep _ _ _ x₀ = x₀
liftRep _ ρ K (↑ x) = ↑ (ρ K x)

liftRep-cong : ∀ {U} {V} {K} {ρ ρ' : Rep U V} → 
  ρ ∼R ρ' → liftRep K ρ ∼R liftRep K ρ'
liftRep-cong ρ-is-ρ' x₀ = refl
liftRep-cong ρ-is-ρ' (↑ x) = cong (var ∘ ↑) (var-inj (ρ-is-ρ' x))

Rep∶LF : LiftFamily
Rep∶LF = record { 
  preOpFamily = Rep∶POF ; 
  lifting = record { 
    liftOp = liftRep ; 
    liftOp-cong = liftRep-cong } ; 
  isLiftFamily = record { 
    liftOp-x₀ = refl ; 
    liftOp-↑ = λ _ → refl } }

infix 70 _〈_〉
_〈_〉 : ∀ {U} {V} {C} {K} → Subexp U C K → Rep U V → Subexp V C K
E 〈 ρ 〉 = LiftFamily.ap Rep∶LF ρ E

liftsRep : ∀ {U V} KK → Rep U V → Rep (extend U KK) (extend V KK)
liftsRep = LiftFamily.liftsOp Rep∶LF

infixl 75 _•R_
_•R_ : ∀ {U} {V} {W} → Rep V W → Rep U V → Rep U W
(ρ' •R ρ) K x = ρ' K (ρ K x)

liftRep-•R : ∀ {U} {V} {W} {K} {ρ' : Rep V W} {ρ : Rep U V} → 
  liftRep K (ρ' •R ρ) ∼R liftRep K ρ' •R liftRep K ρ
liftRep-•R x₀ = refl
liftRep-•R (↑ _) = refl

REP : OpFamily
REP = record { 
  liftFamily = Rep∶LF ; 
  comp = record { 
    _∘_ = _•R_ ; 
    apV-comp = refl ; 
    liftOp-comp' = liftRep-•R } }

•R-congl : ∀ {U V W} {ρ₁ ρ₂ : Rep V W} → ρ₁ ∼R ρ₂ → ∀ (ρ₃ : Rep U V) → ρ₁ •R ρ₃ ∼R ρ₂ •R ρ₃
•R-congl = OpFamily.comp-congl REP

•R-congr : ∀ {U V W} {ρ₁ : Rep V W} {ρ₂ ρ₃ : Rep U V} → ρ₂ ∼R ρ₃ → ρ₁ •R ρ₂ ∼R ρ₁ •R ρ₃
•R-congr {ρ₁ = ρ₁} = OpFamily.comp-congr REP ρ₁

rep-congr : ∀ {U V C K} {ρ ρ' : Rep U V} → ρ ∼R ρ' → ∀ (E : Subexp U C K) → E 〈 ρ 〉 ≡ E 〈 ρ' 〉
rep-congr = OpFamily.ap-congl REP

rep-congl : ∀ {U V C K} {ρ : Rep U V} {E F : Subexp U C K} → E ≡ F → E 〈 ρ 〉 ≡ F 〈 ρ 〉
rep-congl = OpFamily.ap-congr REP

rep-idRep : ∀ {V C K} {E : Subexp V C K} → E 〈 idRep V 〉 ≡ E
rep-idRep = OpFamily.ap-idOp REP

rep-•R : ∀ {U V W C K} (E : Subexp U C K) {σ : Rep V W} {ρ} → E 〈 σ •R ρ 〉 ≡ E 〈 ρ 〉 〈 σ 〉
rep-•R = OpFamily.ap-comp REP

liftRep-idRep : ∀ {V K} → liftRep K (idRep V) ∼R idRep (V , K)
liftRep-idRep = OpFamily.liftOp-idOp REP

liftRep-upRep : ∀ {U V C K L} {σ : Rep U V} (E : Subexp U C K) → E 〈 upRep 〉 〈 liftRep L σ 〉 ≡ E 〈 σ 〉 〈 upRep 〉
liftRep-upRep = OpFamily.liftOp-up REP

--TODO Versions of below for any op-family
rep-•R₃ : ∀ {U V₁ V₂ V₃ C K} (E : Subexp U C K) {ρ₁ : Rep U V₁} {ρ₂ : Rep V₁ V₂} {ρ₃ : Rep V₂ V₃} →
  E 〈 ρ₃ •R ρ₂ •R ρ₁ 〉 ≡ E 〈 ρ₁ 〉 〈 ρ₂ 〉 〈 ρ₃ 〉
rep-•R₃ E {ρ₁} {ρ₂} {ρ₃} =
  let open ≡-Reasoning in
  begin
    E 〈 ρ₃ •R ρ₂ •R ρ₁ 〉
  ≡⟨ rep-•R E ⟩
    E 〈 ρ₁ 〉 〈 ρ₃ •R ρ₂ 〉
  ≡⟨ rep-•R (E 〈 ρ₁ 〉) ⟩
    E 〈 ρ₁ 〉 〈 ρ₂ 〉 〈 ρ₃ 〉
  ∎

rep-•R₄ : ∀ {U} {V1} {V2} {V3} {V4} 
            {ρ1 : Rep U V1} {ρ2 : Rep V1 V2} {ρ3 : Rep V2 V3} {ρ4 : Rep V3 V4} 
            {C} {K} (E : Subexp U C K) →
            E 〈 ρ4 •R ρ3 •R ρ2 •R ρ1 〉 ≡ E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ3 〉 〈 ρ4 〉
rep-•R₄ {ρ1 = ρ1} {ρ2} {ρ3} {ρ4} E = 
  let open ≡-Reasoning in 
  begin
    E 〈 ρ4 •R ρ3 •R ρ2 •R ρ1 〉
      ≡⟨ rep-•R₃ E ⟩
    E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ4 •R ρ3 〉
      ≡⟨ rep-•R (E 〈 ρ1 〉 〈 ρ2 〉) ⟩
    E 〈 ρ1 〉 〈 ρ2 〉 〈 ρ3 〉 〈 ρ4 〉
  ∎
--TODO Make ordering of arguments consistent

infixl 70 _⇑
_⇑ : ∀ {V} {K} {C} {L} → Subexp V C L → Subexp (V , K) C L
E ⇑ = E 〈 upRep 〉

--TODO Version of below for any op-family and foldfunc
ups : ∀ {V} KK → Rep V (snoc-extend V KK)
ups [] = idRep _
ups (KK snoc K) = upRep •R ups KK

infix 70 _⇑⇑
_⇑⇑ : ∀ {V C K KK} → Subexp V C K → Subexp (snoc-extend V KK) C K
_⇑⇑ {KK = KK} E = E 〈 ups KK 〉

liftRep-upRep₂ : ∀ {U} {V} {C} {K} {L} {M} (E : Subexp U C M) {ρ : Rep U V} → E ⇑ ⇑ 〈 liftRep K (liftRep L ρ) 〉 ≡ E 〈 ρ 〉 ⇑ ⇑
liftRep-upRep₂ {K = K} {L} E {ρ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ 〈 liftRep K (liftRep L ρ) 〉
  ≡⟨ liftRep-upRep (E ⇑) ⟩
    E ⇑ 〈 liftRep L ρ 〉 ⇑
  ≡⟨ rep-congl (liftRep-upRep E) ⟩
    E 〈 ρ 〉 ⇑ ⇑
  ∎

liftRep-upRep₃ : ∀ {U} {V} {C} {K} {L} {M} {N} (E : Subexp U C N) {ρ : Rep U V} → 
  E ⇑ ⇑ ⇑ 〈 liftRep K (liftRep L (liftRep M ρ)) 〉 ≡ E 〈 ρ 〉 ⇑ ⇑ ⇑
liftRep-upRep₃ {K = K} {L} {M} E {ρ} = let open ≡-Reasoning in 
  begin
    E ⇑ ⇑ ⇑ 〈 liftRep K (liftRep L (liftRep M ρ)) 〉
  ≡⟨ liftRep-upRep₂ (E ⇑) ⟩
    E ⇑ 〈 liftRep M ρ 〉 ⇑ ⇑
  ≡⟨ rep-congl (rep-congl (liftRep-upRep E)) ⟩
    E 〈 ρ 〉 ⇑ ⇑ ⇑
  ∎

Types-rep : ∀ {U V KK} → Types U KK → Rep U V → Types V KK
Types-rep [] _ = []
Types-rep (B , BB) ρ = B 〈 ρ 〉 , Types-rep BB (liftRep _ ρ)
