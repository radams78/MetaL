open import Grammar.Base
  
module Grammar.Substitution.BotSub (G : Grammar) where
open import Prelims
open Grammar G
open import Grammar.OpFamily G
open import Grammar.Replacement G
open import Grammar.Substitution.PreOpFamily G
open import Grammar.Substitution.Lifting G
open import Grammar.Substitution.LiftFamily G
open import Grammar.Substitution.OpFamily G
open LiftFamily

botSub : ∀ {V} {KK} → HetsnocList (VExpression V) KK → Sub (snoc-extend V KK) V
botSub {KK = []} _ _ x = var x
botSub {KK = _ snoc _} (_ snoc E) _ x₀ = E
botSub {KK = _ snoc _} (EE snoc _) L (↑ x) = botSub EE L x

infix 65 x₀:=_
x₀:=_ : ∀ {V} {K} → Expression V (varKind K) → Sub (V , K) V
x₀:= E = botSub ([] snoc E)

botSub-up' : ∀ {F} {V} {K} {E : Expression V (varKind K)} (comp : Composition SubLF F SubLF) →
  Composition._∘_ comp (x₀:= E) (up F) ∼ idSub V
botSub-up' {F} {V} {K} {E} comp x = let open ≡-Reasoning in 
  begin
    (Composition._∘_ comp (x₀:= E) (up F)) _ x
  ≡⟨ Composition.apV-comp comp ⟩
    apV F (up F) x ⟦ x₀:= E ⟧
  ≡⟨ sub-congl (apV-up F) ⟩
    var x
  ∎

botSub-up : ∀ {F} {V} {K} {C} {L} {E : Expression V (varKind K)} (comp : Composition SubLF F SubLF) {E' : Subexp V C L} →
  ap F (up F) E' ⟦ x₀:= E ⟧ ≡ E'
botSub-up {F} {V} {K} {C} {L} {E} comp {E'} = let open ≡-Reasoning in
  begin
    ap F (up F) E' ⟦ x₀:= E ⟧
  ≡⟨⟨ Composition.ap-comp comp E' ⟩⟩
    E' ⟦ Composition._∘_ comp (x₀:= E) (up F) ⟧
  ≡⟨ sub-congr E' (botSub-up' comp)⟩
    E' ⟦ idSub V ⟧
  ≡⟨ sub-idSub ⟩
    E'
  ∎

comp-botSub' : ∀ {F} {U} {V} {K} {E : Expression U (varKind K)} 
  (comp₁ : Composition F SubLF SubLF) 
  (comp₂ : Composition SubLF F SubLF)
  {σ : Op F U V} →
  Composition._∘_ comp₁ σ (x₀:= E) ∼ Composition._∘_ comp₂ (x₀:= (ap F σ E)) (liftOp F K σ)
comp-botSub' {F} {U} {V} {K} {E} comp₁ comp₂ {σ} x₀ = let open ≡-Reasoning in 
  begin
    (Composition._∘_ comp₁ σ (x₀:= E)) _ x₀
  ≡⟨ Composition.apV-comp comp₁ ⟩
    ap F σ E
  ≡⟨⟨ sub-congl (liftOp-x₀ F) ⟩⟩
    (apV F (liftOp F K σ) x₀) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-comp comp₂ ⟩⟩
    (Composition._∘_ comp₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ x₀
  ∎
comp-botSub' {F} {U} {V} {K} {E} comp₁ comp₂ {σ} (↑ x) = let open ≡-Reasoning in 
  begin
    (Composition._∘_ comp₁ σ (x₀:= E)) _ (↑ x)
  ≡⟨ Composition.apV-comp comp₁ ⟩
    apV F σ x
  ≡⟨⟨ sub-idSub ⟩⟩
    apV F σ x ⟦ idSub V ⟧
  ≡⟨⟨ sub-congr (apV F σ x) (botSub-up' comp₂) ⟩⟩
    apV F σ x ⟦ Composition._∘_ comp₂ (x₀:= (ap F σ E)) (up F) ⟧
  ≡⟨ Composition.ap-comp comp₂ (apV F σ x) ⟩
    ap F (up F) (apV F σ x) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ sub-congl (liftOp-↑ F x) ⟩⟩
    (apV F (liftOp F K σ) (↑ x)) ⟦ x₀:= (ap F σ E) ⟧
  ≡⟨⟨ Composition.apV-comp comp₂ ⟩⟩
    (Composition._∘_ comp₂ (x₀:= (ap F σ E)) (liftOp F K σ)) _ (↑ x)
  ∎

comp-botSub : ∀ {F} {U} {V} {K} {C} {L} 
  {E : Expression U (varKind K)} {E' : Subexp (U , K) C L} {σ : Op F U V} →
  Composition F SubLF SubLF →
  Composition SubLF F SubLF →
  ap F σ (E' ⟦ x₀:= E ⟧) ≡ (ap F (liftOp F K σ) E') ⟦ x₀:= (ap F σ E) ⟧
comp-botSub {E' = E'} comp₁ comp₂ = ap-comp-sim comp₁ comp₂ (comp-botSub' comp₁ comp₂) E'

•RS-botSub' : ∀ {U} {V} {K} {F : Expression U (varKind K)} {ρ : Rep U V} →
  ρ •RS x₀:= F ∼ x₀:= F 〈 ρ 〉 •SR liftRep K ρ
•RS-botSub' = comp-botSub' COMPRS COMPSR

•RS-botSub : ∀ {U} {V} {C} {K} {L} (E : Subexp (U , K) C L) {F : Expression U (varKind K)} {ρ : Rep U V} →
  E ⟦ x₀:= F ⟧ 〈 ρ 〉 ≡ E 〈 liftRep K ρ 〉 ⟦ x₀:= (F 〈 ρ 〉) ⟧
•RS-botSub E = comp-botSub {E' = E} COMPRS COMPSR

•-botSub'' : ∀ {U} {V} {C} {K} {L} 
  {E : Expression U (varKind K)} {σ : Sub U V} (F : Subexp (U , K) C L) →
   F ⟦ x₀:= E ⟧ ⟦ σ ⟧ ≡ F ⟦ liftSub K σ ⟧ ⟦ x₀:= (E ⟦ σ ⟧) ⟧
--TODO Better name
•-botSub'' F = let COMP = OpFamily.comp SUB in comp-botSub {E' = F} COMP COMP

botSub-upRep' : ∀ {V K} (E : VExpression V K) → x₀:= E •SR upRep ∼ idSub V
botSub-upRep' E = botSub-up' {E = E} COMPSR

botSub-upRep : ∀ {U} {C} {K} {L}
  (E : Subexp U C K) {F : Expression U (varKind L)} → 
  E 〈 upRep 〉 ⟦ x₀:= F ⟧ ≡ E
botSub-upRep _ = botSub-up COMPSR

x₂:=_,x₁:=_,x₀:=_ : ∀ {V} {K1} {K2} {K3} → Expression V (varKind K1) → Expression V (varKind K2) → Expression V (varKind K3) → Sub (((V , K1) , K2) , K3) V
x₂:=_,x₁:=_,x₀:=_ M1 M2 M3 = botSub ((([] snoc M1) snoc M2) snoc M3)

botSub₃-upRep₃' : ∀ {V K₁ K₂ K₃} {N₁ : VExpression V K₁} {N₂ : VExpression V K₂} {N₃ : VExpression V K₃} →
  (x₂:= N₁ ,x₁:= N₂ ,x₀:= N₃) •SR upRep •SR upRep  •SR upRep ∼ idSub V
botSub₃-upRep₃' x₀ = refl
botSub₃-upRep₃' (↑ x₀) = refl
botSub₃-upRep₃' (↑ (↑ x₀)) = refl
botSub₃-upRep₃' (↑ (↑ (↑ _))) = refl

botSub-upRep₃ : ∀ {V} {K1} {K2} {K3} {L} {M : Expression V L} 
  {N1 : Expression V (varKind K1)} {N2 : Expression V (varKind K2)} {N3 : Expression V (varKind K3)} →
  M ⇑ ⇑ ⇑ ⟦ x₂:= N1 ,x₁:= N2 ,x₀:= N3 ⟧ ≡ M
botSub-upRep₃ {V} {K1} {K2} {K3} {L} {M} {N1} {N2} {N3} = let open ≡-Reasoning in 
  begin
    M ⇑ ⇑ ⇑ ⟦ x₂:= N1 ,x₁:= N2 ,x₀:= N3 ⟧
  ≡⟨⟨ sub-•SR (M ⇑ ⇑) ⟩⟩
    M ⇑ ⇑ ⟦ (x₂:= N1 ,x₁:= N2 ,x₀:= N3) •SR upRep ⟧
  ≡⟨⟨ sub-•SR (M ⇑) ⟩⟩
    M ⇑ ⟦ (x₂:= N1 ,x₁:= N2 ,x₀:= N3) •SR upRep •SR upRep ⟧
  ≡⟨⟨ sub-•SR M ⟩⟩
    M ⟦ (x₂:= N1 ,x₁:= N2 ,x₀:= N3) •SR upRep •SR upRep •SR upRep ⟧
  ≡⟨ sub-congr M (botSub₃-upRep₃' {N₁ = N1} {N2} {N3}) ⟩
    M ⟦ idSub V ⟧
  ≡⟨ sub-idSub ⟩
    M
  ∎

botSub₃-liftRep₃' : ∀ {U} {V} {K2} {K1} {K0}
  {M2 : Expression U (varKind K1)} {M1 : Expression U (varKind K2)} {M0 : Expression U (varKind K0)} {ρ : Rep U V} →
  (x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉) •SR liftRep _ (liftRep _ (liftRep _ ρ))
  ∼ ρ •RS (x₂:= M2 ,x₁:= M1 ,x₀:= M0)
botSub₃-liftRep₃' x₀ = refl
botSub₃-liftRep₃' (↑ x₀) = refl
botSub₃-liftRep₃' (↑ (↑ x₀)) = refl 
botSub₃-liftRep₃' (↑ (↑ (↑ x))) = refl

botSub₃-liftRep₃ : ∀ {U} {V} {K2} {K1} {K0} {L}
  {M2 : Expression U (varKind K2)} {M1 : Expression U (varKind K1)} {M0 : Expression U (varKind K0)} {ρ : Rep U V} (N : Expression (((U , K2) , K1) , K0) L) →
  N 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉 ⟦ x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉 ⟧
  ≡ N ⟦ x₂:= M2 ,x₁:= M1 ,x₀:= M0 ⟧ 〈 ρ 〉
botSub₃-liftRep₃ {M2 = M2} {M1} {M0} {ρ} N = let open ≡-Reasoning in
              begin
                N 〈 liftRep _ (liftRep _ (liftRep _ ρ)) 〉 ⟦ x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉 ⟧
              ≡⟨⟨ sub-•SR N ⟩⟩
                N ⟦ (x₂:= M2 〈 ρ 〉 ,x₁:= M1 〈 ρ 〉 ,x₀:= M0 〈 ρ 〉) •SR liftRep _ (liftRep _ (liftRep _ ρ)) ⟧
              ≡⟨ sub-congr N botSub₃-liftRep₃' ⟩
                N ⟦ ρ •RS (x₂:= M2 ,x₁:= M1 ,x₀:= M0) ⟧
              ≡⟨ sub-•RS N ⟩
                N ⟦ x₂:= M2 ,x₁:= M1 ,x₀:= M0 ⟧ 〈 ρ 〉
              ∎
--TODO General lemma for this

botSub-liftSub₃' : ∀ {U V L₂ L₁ L₀} {F₂ : VExpression U L₂} {F₁ : VExpression U L₁} {F₀ : VExpression U L₀} {σ : Sub U V} →
  (x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧) • liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ∼ σ • (x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀)
botSub-liftSub₃' x₀ = refl
botSub-liftSub₃' (↑ x₀) = refl
botSub-liftSub₃' (↑ (↑ x₀)) = refl
botSub-liftSub₃' (↑ (↑ (↑ x))) = botSub-upRep₃

botSub-liftSub₃ : ∀ {U V C K L₂ L₁ L₀} {E : Subexp (((U , L₂) , L₁) , L₀) C K} {F₂ : VExpression U L₂} {F₁ : VExpression U L₁} {F₀ : VExpression U L₀} {σ : Sub U V} →
  E ⟦ liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ⟧ ⟦ x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧ ⟧ ≡ E ⟦ x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀ ⟧ ⟦ σ ⟧
botSub-liftSub₃ {L₂ = L₂} {L₁} {L₀} {E} {F₂} {F₁} {F₀} {σ} = let open ≡-Reasoning in 
  begin
    E ⟦ liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ⟧ ⟦ x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧ ⟧
  ≡⟨⟨ sub-• E ⟩⟩
    E ⟦ (x₂:= F₂ ⟦ σ ⟧ ,x₁:= F₁ ⟦ σ ⟧ ,x₀:= F₀ ⟦ σ ⟧) • liftSub L₀ (liftSub L₁ (liftSub L₂ σ)) ⟧
  ≡⟨ sub-congr E botSub-liftSub₃' ⟩
    E ⟦ σ • (x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀) ⟧
  ≡⟨ sub-• E ⟩
    E ⟦ x₂:= F₂ ,x₁:= F₁ ,x₀:= F₀ ⟧ ⟦ σ ⟧
  ∎

botSub₃-upRep₂' : ∀ {V K₂ K₁ K₀} {M₂ : VExpression V K₂} {M₁ : VExpression V K₁} {M₀ : VExpression V K₀} →
  (x₂:= M₂ ,x₁:= M₁ ,x₀:= M₀) •SR upRep •SR upRep ∼ x₀:= M₂
botSub₃-upRep₂' x₀ = refl
botSub₃-upRep₂' (↑ x₀) = refl
botSub₃-upRep₂' (↑ (↑ x₀)) = refl
botSub₃-upRep₂' (↑ (↑ (↑ x))) = refl

