module PHOML.Grammar.AddPath where
open import Data.Nat
open import Prelims
open import PHOML.Grammar.Base
open import PHOML.Grammar.Const

addpath : ∀ {V} → Context V → Type → Context (extend V pathDom)
addpath Γ A = Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀

--TODO Reverse sign on replacements
upRep₃-addpath-typed : ∀ {V} {Γ : Context V} A → upRep •R upRep •R upRep ∶ Γ ⇒R addpath Γ A
upRep₃-addpath-typed A = upRep₃-typed {A1 = ty A} {A2 = ty A} {A3 = var x₁ ≡〈 A 〉 var x₀}

sub↖ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (extend V pathDom)
sub↖ σ _ x₀ = var x₂
sub↖ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

sub↖-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↖ ρ ∼ sub↖ σ
sub↖-cong ρ∼σ x₀ = refl
sub↖-cong ρ∼σ (↑ x) = rep-congl (rep-congl (rep-congl (ρ∼σ x))) -- TODO Build as setoid function

sub↖-•RS : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
  sub↖ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↖ σ
sub↖-•RS x₀ = refl
sub↖-•RS {σ = σ} (↑ x) = ≡-sym (liftRep-upRep₃ (σ _ x))

sub↖-comp : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↖ (σ • ρ) ∼ liftsSub pathDom σ • sub↖ ρ
sub↖-comp x₀ = refl
sub↖-comp {σ = σ} {ρ} (↑ x) = ≡-sym (liftSub-upRep₃ (ρ _ x))

sub↗ : ∀ {U} {V} → Sub U V → Sub (U , -Term) (((V , -Term) , -Term) , -Path)
sub↗ σ _ x₀ = var x₁
sub↗ σ _ (↑ x) = σ _ x ⇑ ⇑ ⇑

sub↗-cong : ∀ {U} {V} {ρ σ : Sub U V} → ρ ∼ σ → sub↗ ρ ∼ sub↗ σ
sub↗-cong ρ∼σ x₀ = refl
sub↗-cong ρ∼σ (↑ x) = rep-congl (rep-congl (rep-congl (ρ∼σ x))) -- TODO Build as setoid function

sub↗-•RS : ∀ {U} {V} {W} {ρ : Rep V W} {σ : Sub U V} →
  sub↗ (ρ •RS σ) ∼ liftRep -Path (liftRep -Term (liftRep -Term ρ)) •RS sub↗ σ
sub↗-•RS x₀ = refl
sub↗-•RS {σ = σ} (↑ x) = ≡-sym (liftRep-upRep₃ (σ _ x))

sub↗-comp : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↗ (σ • ρ) ∼ liftsSub pathDom σ • sub↗ ρ
sub↗-comp x₀ = refl
sub↗-comp {σ = σ} {ρ} (↑ x) = ≡-sym (liftSub-upRep₃ (ρ _ x))

--REFACTOR Duplication

sub↖-•SR : ∀ {U V W} {σ : Sub V W} {ρ : Rep U V} → sub↖ (σ •SR ρ) ∼ sub↖ σ •SR liftRep _ ρ
sub↖-•SR x₀ = refl
sub↖-•SR (↑ x) = refl

sub↗-•SR : ∀ {U V W} {σ : Sub V W} {ρ : Rep U V} → sub↗ (σ •SR ρ) ∼ sub↗ σ •SR liftRep _ ρ
sub↗-•SR x₀ = refl
sub↗-•SR (↑ x) = refl

sub↖-• : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↖ (σ • ρ) ∼ sub↖ σ • liftSub _ ρ
sub↖-• x₀ = refl
sub↖-• {σ = σ} {ρ} (↑ x) = let open ≡-Reasoning in 
  begin
    ρ _ x ⟦ σ ⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (sub-•RS (ρ _ x))) ⟩⟩
    ρ _ x ⟦ upRep •RS σ ⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (sub-•RS (ρ _ x)) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS σ) ⟧ ⇑
  ≡⟨⟨ sub-•RS (ρ _ x) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS (upRep •RS σ)) ⟧
  ≡⟨⟩
    ρ _ x ⟦ sub↖ σ •SR upRep ⟧
  ≡⟨ sub-•SR (ρ _ x) ⟩
    ρ _ x ⇑ ⟦ sub↖ σ ⟧
  ∎

sub↗-• : ∀ {U V W} {σ : Sub V W} {ρ : Sub U V} → sub↗ (σ • ρ) ∼ sub↗ σ • liftSub _ ρ
sub↗-• x₀ = refl
sub↗-• {σ = σ} {ρ} (↑ x) = let open ≡-Reasoning in 
  begin
    ρ _ x ⟦ σ ⟧ ⇑ ⇑ ⇑
  ≡⟨⟨ rep-congl (rep-congl (sub-•RS (ρ _ x))) ⟩⟩
    ρ _ x ⟦ upRep •RS σ ⟧ ⇑ ⇑
  ≡⟨⟨ rep-congl (sub-•RS (ρ _ x)) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS σ) ⟧ ⇑
  ≡⟨⟨ sub-•RS (ρ _ x) ⟩⟩
    ρ _ x ⟦ upRep •RS (upRep •RS (upRep •RS σ)) ⟧
  ≡⟨⟩
    ρ _ x ⟦ sub↗ σ •SR upRep ⟧
  ≡⟨ sub-•SR (ρ _ x) ⟩
    ρ _ x ⇑ ⟦ sub↗ σ ⟧
  ∎

sub↖-botSub : ∀ {U V} {σ : Sub U V} {M N P} → σ • (x₀:= M) ∼ (x₂:= M ⟦ σ ⟧ ,x₁:= N ,x₀:= P) • sub↖ σ
sub↖-botSub x₀ = refl
sub↖-botSub {σ = σ} {M} {N} {P} (↑ x) = ≡-sym botSub-upRep₃

sub↗-botSub : ∀ {U V} {σ : Sub U V} {M N P} → σ • (x₀:= M) ∼ (x₂:= N ,x₁:= M ⟦ σ ⟧ ,x₀:= P) • sub↗ σ
sub↗-botSub x₀ = refl
sub↗-botSub {σ = σ} {M} {N} {P} (↑ x) = ≡-sym botSub-upRep₃

liftsRep-sub↖id : ∀ {U V} {ρ : Rep U V} → liftsRep pathDom ρ •RS sub↖ (idSub U) ∼ sub↖ (idSub V) •SR liftRep -Term ρ
liftsRep-sub↖id x₀ = refl
liftsRep-sub↖id (↑ _) = refl

liftsRep-sub↗id : ∀ {U V} {ρ : Rep U V} → liftsRep pathDom ρ •RS sub↗ (idSub U) ∼ sub↗ (idSub V) •SR liftRep -Term ρ
liftsRep-sub↗id x₀ = refl
liftsRep-sub↗id (↑ _) = refl

liftsRep-sub↖ : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} →
  liftsRep pathDom ρ •RS sub↖ σ ∼ sub↖ (ρ •RS σ)
liftsRep-sub↖ x₀ = refl
liftsRep-sub↖ {σ = σ} (↑ x) = liftRep-upRep₃ (σ _ x)

liftsRep-sub↗ : ∀ {U V W} {ρ : Rep V W} {σ : Sub U V} →
  liftsRep pathDom ρ •RS sub↗ σ ∼ sub↗ (ρ •RS σ)
liftsRep-sub↗ x₀ = refl
liftsRep-sub↗ {σ = σ} (↑ x) = liftRep-upRep₃ (σ _ x)

botSub₃-sub↖ : ∀ {U V} {M N : Term V} {P} {σ : Sub U V} →
  (x₂:= M ,x₁:= N ,x₀:= P) • sub↖ σ ∼ extendSub σ M
botSub₃-sub↖ x₀ = refl
botSub₃-sub↖ (↑ x) = botSub-upRep₃

botSub₃-sub↗ : ∀ {U V} {M N : Term V} {P} {σ : Sub U V} →
  (x₂:= M ,x₁:= N ,x₀:= P) • sub↗ σ ∼ extendSub σ N
botSub₃-sub↗ x₀ = refl
botSub₃-sub↗ (↑ x) = botSub-upRep₃

sub↖-upRep' : ∀ {U V} {σ : Sub U V} → sub↖ σ •SR upRep ∼ upRep •R upRep •R upRep •RS σ
sub↖-upRep' {σ = σ} x = ≡-sym (rep-•R₃ (σ _ x))

sub↖-upRep : ∀ {U V C K} {E : Subexp U C K} {σ : Sub U V} → E ⇑ ⟦ sub↖ σ ⟧ ≡ E ⟦ σ ⟧ ⇑ ⇑ ⇑
sub↖-upRep {U} {V} {C} {K} {E} {σ} = let open ≡-Reasoning in
  begin
    E ⇑ ⟦ sub↖ σ ⟧
  ≡⟨⟨ sub-•SR E ⟩⟩
    E ⟦ sub↖ σ •SR upRep ⟧
  ≡⟨ sub-congr E (sub↖-upRep' {σ = σ}) ⟩
    E ⟦ upRep •R upRep •R upRep •RS σ ⟧
  ≡⟨ sub-•RS E ⟩
    E ⟦ σ ⟧ 〈 upRep •R upRep •R upRep 〉
  ≡⟨ rep-•R₃ (E ⟦ σ ⟧) ⟩
    E ⟦ σ ⟧ ⇑ ⇑ ⇑
  ∎

sub↗-upRep' : ∀ {U V} {σ : Sub U V} → sub↗ σ •SR upRep ∼ upRep •R upRep •R upRep •RS σ
sub↗-upRep' {σ = σ} x = ≡-sym (rep-•R₃ (σ _ x))

sub↗-upRep : ∀ {U V C K} {E : Subexp U C K} {σ : Sub U V} → E ⇑ ⟦ sub↗ σ ⟧ ≡ E ⟦ σ ⟧ ⇑ ⇑ ⇑
sub↗-upRep {U} {V} {C} {K} {E} {σ} = let open ≡-Reasoning in
  begin
    E ⇑ ⟦ sub↗ σ ⟧
  ≡⟨⟨ sub-•SR E ⟩⟩
    E ⟦ sub↗ σ •SR upRep ⟧
  ≡⟨ sub-congr E (sub↗-upRep' {σ = σ}) ⟩
    E ⟦ upRep •R upRep •R upRep •RS σ ⟧
  ≡⟨ sub-•RS E ⟩
    E ⟦ σ ⟧ 〈 upRep •R upRep •R upRep 〉
  ≡⟨ rep-•R₃ (E ⟦ σ ⟧) ⟩
    E ⟦ σ ⟧ ⇑ ⇑ ⇑
  ∎

private sub↖-decomp₁ : ∀ {V} {K₁} {K₂} {K₃} → x₀:= var (x₂ {V} {K₁} {K₂} {K₃}) •SR liftRep K₁ upRep •SR liftRep K₁ upRep •SR liftRep K₁ upRep ∼ rep2sub (upRep •R upRep)
sub↖-decomp₁ x₀ = refl
sub↖-decomp₁ (↑ x) = refl

private sub↖-decomp₂ : ∀ {U} {V} {σ : Sub U V} → rep2sub (upRep •R upRep) • liftSub _ σ ∼ sub↖ σ
sub↖-decomp₂ x₀ = refl
sub↖-decomp₂ {σ = σ} (↑ x) = let open ≡-Reasoning in 
  begin
    σ _ x ⇑ ⟦ rep2sub (upRep •R upRep) ⟧
  ≡⟨⟨ rep-is-sub (σ _ x ⇑) ⟩⟩
    σ _ x ⇑ 〈 upRep •R upRep 〉
  ≡⟨ rep-•R (σ _ x ⇑) ⟩
    σ _ x ⇑ ⇑ ⇑
  ∎

private sub↖-decomp' : ∀ {U} {V} {σ : Sub U V} →
                     x₀:= var x₂ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ
                     ∼ sub↖ σ
sub↖-decomp' {U} {V} {σ} = let open EqReasoning (OpFamily.OP SUB (U , -Term) (extend V pathDom)) in 
  begin
    x₀:= var x₂ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ
  ≈⟨ •-congl sub↖-decomp₁ (liftSub _ σ) ⟩
    rep2sub (upRep •R upRep) • liftSub _ σ
  ≈⟨ sub↖-decomp₂ ⟩
    sub↖ σ
  ∎

sub↖-decomp : ∀ {U V C K} {E : Subexp (U , -Term) C K} {σ : Sub U V} →
  E ⟦ sub↖ σ ⟧ ≡ E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₂ ⟧
sub↖-decomp {E = E} {σ} = let open ≡-Reasoning in 
  begin
    E ⟦ sub↖ σ ⟧
  ≡⟨⟨ sub-congr E sub↖-decomp' ⟩⟩
    E ⟦ x₀:= var x₂ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ ⟧
  ≡⟨ sub-• E ⟩
    E ⟦ liftSub -Term σ ⟧ ⟦ x₀:= var x₂ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
  ≡⟨ sub-•SR (E ⟦ liftSub _ σ ⟧) ⟩
    E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₂ •SR liftRep _ upRep •SR liftRep _ upRep ⟧
  ≡⟨ sub-•SR (E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉) ⟩
    E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₂ •SR liftRep _ upRep ⟧
  ≡⟨ sub-•SR (E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉) ⟩
    E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₂ ⟧
  ∎

private sub↗-decomp₁ : ∀ {V} {K₁} {K₂} {K₃} → x₀:= var (x₁ {V , K₃} {K₁} {K₂}) •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR upRep ∼ rep2sub (upRep •R upRep •R upRep)
sub↗-decomp₁ x₀ = refl
sub↗-decomp₁ (↑ x) = refl

sub↗-decomp' : ∀ {U V} {σ : Sub U V} → sub↗ σ ∼ x₀:= var x₁ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ
sub↗-decomp' x₀ = refl
sub↗-decomp' {σ = σ} (↑ x) = let open ≡-Reasoning in 
  begin
    σ _ x ⇑ ⇑ ⇑
  ≡⟨⟨ rep-•R₃ (σ _ x) ⟩⟩
    σ _ x 〈 upRep •R upRep •R upRep 〉
  ≡⟨ rep-is-sub (σ _ x) ⟩
    σ _ x ⟦ rep2sub (upRep •R upRep •R upRep) ⟧
  ≡⟨ sub-congr (σ _ x) sub↗-decomp₁ ⟩
    σ _ x ⟦ x₀:= var x₁ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep •SR upRep ⟧
  ≡⟨ sub-•SR (σ _ x) ⟩
    σ _ x ⇑ ⟦ x₀:= var x₁ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
  ∎

sub↗-decomp : ∀ {U V C K} {E : Subexp (U , -Term) C K} {σ : Sub U V} →
  E ⟦ sub↗ σ ⟧ ≡ E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₁ ⟧
sub↗-decomp {E = E} {σ = σ} = let open ≡-Reasoning in 
  begin
    E ⟦ sub↗ σ ⟧
  ≡⟨ sub-congr E sub↗-decomp' ⟩
    E ⟦ x₀:= var x₁ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep • liftSub _ σ ⟧
  ≡⟨ sub-• E ⟩
    E ⟦ liftSub -Term σ ⟧ ⟦ x₀:= var x₁ •SR liftRep _ upRep •SR liftRep _ upRep •SR liftRep _ upRep ⟧
  ≡⟨ sub-•SR (E ⟦ liftSub -Term σ ⟧) ⟩
    E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₁ •SR liftRep _ upRep •SR liftRep _ upRep ⟧
  ≡⟨ sub-•SR (E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉) ⟩
    E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₁ •SR liftRep _ upRep ⟧
  ≡⟨ sub-•SR (E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉) ⟩
    E ⟦ liftSub -Term σ ⟧ 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 〈 liftRep -Term upRep 〉 ⟦ x₀:= var x₁ ⟧
  ∎

botSub₃-sub↖id : ∀ {V} {M N : Term V} {P} → (x₂:= M ,x₁:= N ,x₀:= P) • sub↖ (idSub V) ∼ x₀:= M
botSub₃-sub↖id x₀ = refl
botSub₃-sub↖id (↑ x) = refl

botSub₃-sub↗id : ∀ {V} {M N : Term V} {P} → (x₂:= M ,x₁:= N ,x₀:= P) • sub↗ (idSub V) ∼ x₀:= N
botSub₃-sub↗id x₀ = refl
botSub₃-sub↗id (↑ x) = refl
