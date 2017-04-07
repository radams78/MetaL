module PHOML.Rules where
open import Data.Product using (_×_)
open import Prelims
open import PHOML.Grammar
open import PHOML.Red

infix 10 _⊢_∶_
data valid : ∀ {V} → Context V → Set
data _⊢_∶_ : ∀ {V} {K} → Context V → 
  Expression V (varKind K) → 
  Expression V (parent K) → Set

----------------------------------------------------
---- Contexts
----------------------------------------------------

data valid where
  〈〉R : 

  -----------
    valid 〈〉

  ctxTR : ∀ {V} {Γ : Context V} {A : Type} → 

      valid Γ → 
  ------------------
    valid (Γ ,T A)

  ctxPR : ∀ {V} {Γ : Context V} {φ : Term V} → 

     Γ ⊢ φ ∶ ty Ω → 
  ------------------
    valid (Γ ,P φ)

  ctxER : ∀ {V} {Γ : Context V} {M N : Term V} {A : Type} →

    Γ ⊢ M ∶ ty A → Γ ⊢ N ∶ ty A → 
  --------------------------------
        valid (Γ ,E M ≡〈 A 〉 N)

data _⊢_∶_ where

  varR : ∀ {V} {K} {Γ : Context V} (x : Var V K)

      (validΓ : valid Γ)     → 
  ------------------------------
    Γ ⊢ var x ∶ typeof x Γ

----------------------------------------------------
---- Terms
----------------------------------------------------

  ⊥R : ∀ {V} {Γ : Context V}

   (validΓ : valid Γ) →
  --------------------
       Γ ⊢ ⊥ ∶ ty Ω

  ⊃R : ∀ {V} {Γ : Context V} {φ ψ : Term V}

    (Γ⊢φ∶Ω : Γ ⊢ φ ∶ ty Ω) (Γ⊢ψ∶Ω : Γ ⊢ ψ ∶ ty Ω) →
  ------------------------------------------
                 Γ ⊢ φ ⊃ ψ ∶ ty Ω

  appTR : ∀ {V} {Γ : Context V} {M N : Term V} {A} {B} 

    (Γ⊢M∶A⇛B : Γ ⊢ M ∶ ty (A ⇛ B)) (Γ⊢N∶A : Γ ⊢ N ∶ ty A) →
  ----------------------------------------------------------
                  Γ ⊢ appT M N ∶ ty B

  ΛTR : ∀ {V} {Γ : Context V} {A} {M : Term (V , -Term)} {B}

    (Γ,A⊢M∶B : Γ , ty A ⊢ M ∶ ty B) → 
  -------------------------------------
           Γ ⊢ ΛT A M ∶ ty (A ⇛ B)

----------------------------------------------------
---- Proofs
----------------------------------------------------

  appPR : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ ψ : Term V} →

    Γ ⊢ δ ∶ φ ⊃ ψ → Γ ⊢ ε ∶ φ → 
  -------------------------------
         Γ ⊢ appP δ ε ∶ ψ

  ΛPR : ∀ {V} {Γ : Context V} {δ : Proof (V , -Proof)} {φ ψ : Term V} → 

    Γ ⊢ φ ∶ ty Ω → Γ ⊢ ψ ∶ ty Ω → Γ ,P φ ⊢ δ ∶ ψ 〈 upRep 〉 → 
  -----------------------------------------------------------
                    Γ ⊢ ΛP φ δ ∶ φ ⊃ ψ

  convPR : ∀ {V} {Γ : Context V} {δ : Proof V} {φ ψ : Term V} →

    Γ ⊢ δ ∶ φ → Γ ⊢ ψ ∶ ty Ω → 
                                φ ≃ ψ → 
  -----------------------------
          Γ ⊢ δ ∶ ψ

----------------------------------------------------
---- Paths
----------------------------------------------------

  refR : ∀ {V} {Γ : Context V} {M : Term V} {A : Type} → 

               Γ ⊢ M ∶ ty A → 
  ---------------------------------------
           Γ ⊢ reff M ∶ M ≡〈 A 〉 M

  ⊃*R : ∀ {V} {Γ : Context V} {P Q : Expression V (varKind -Path)} {φ φ' ψ ψ' : Term V} →

    Γ ⊢ P ∶ φ ≡〈 Ω 〉 φ' → Γ ⊢ Q ∶ ψ ≡〈 Ω 〉 ψ' →
  ----------------------------------------------
      Γ ⊢ P ⊃* Q ∶ (φ ⊃ ψ) ≡〈 Ω 〉 (φ' ⊃ ψ')

  univR : ∀ {V} {Γ : Context V} {δ ε : Proof V} {φ ψ : Term V} →

    Γ ⊢ δ ∶ φ ⊃ ψ → Γ ⊢ ε ∶ ψ ⊃ φ → 
  -----------------------------------
     Γ ⊢ univ φ ψ δ ε ∶ φ ≡〈 Ω 〉 ψ

  plusR : ∀ {V} {Γ : Context V} {P : Expression V (varKind -Path)} {φ ψ : Term V} →

    Γ ⊢ P ∶ φ ≡〈 Ω 〉 ψ → 
  -----------------------
    Γ ⊢ plus P ∶ φ ⊃ ψ

  minusR : ∀ {V} {Γ : Context V} {P : Expression V (varKind -Path)} {φ ψ : Term V} →

    Γ ⊢ P ∶ φ ≡〈 Ω 〉 ψ → 
  -----------------------
    Γ ⊢ minus P ∶ ψ ⊃ φ

  lllR : ∀ {V} {Γ : Context V} {A B : Type} {M N : Term V} 
    {P : Path (((V , -Term) , -Term) , -Path)} →

                   Γ ⊢ M ∶ ty (A ⇛ B) → Γ ⊢ N ∶ ty (A ⇛ B) →
    Γ ,T A ,T A ,E var x₁ ≡〈 A 〉 var x₀
        ⊢ P ∶ appT (M ⇑ ⇑ ⇑ ) (var x₂) ≡〈 B 〉 appT (N ⇑ ⇑ ⇑) (var x₁) →
  ------------------------------------------------------------------------
                       Γ ⊢ λλλ A P ∶ M ≡〈 A ⇛ B 〉 N

  appER : ∀ {V} {Γ : Context V} {P Q : Path V} {M M' N N' : Term V} {A B : Type} →

           Γ ⊢ N ∶ ty A → Γ ⊢ N' ∶ ty A →
    Γ ⊢ P ∶ M ≡〈 A ⇛ B 〉 M' → Γ ⊢ Q ∶ N ≡〈 A 〉 N' →
  -------------------------------------------------
    Γ ⊢ app* N N' P Q ∶ appT M N ≡〈 B 〉 appT M' N'

  convER : ∀ {V} {Γ : Context V} {P : Path V} {M M' N N' : Term V} {A : Type}

           (Γ⊢P∶M≡N : Γ ⊢ P ∶ M ≡〈 A 〉 N) (Γ⊢M':A : Γ ⊢ M' ∶ ty A) (Γ⊢N'∶A : Γ ⊢ N' ∶ ty A)
                                                                                            (M≃M' : M ≃ M') (N≃N' : N ≃ N') →
          ---------------------------------------------------------------------------------
                                    Γ ⊢ P ∶ M' ≡〈 A 〉 N'

change-type : ∀ {V} {Γ} {K} {M : Expression V (varKind K)} {A} {B} → 
  Γ ⊢ M ∶ A → A ≡ B → Γ ⊢ M ∶ B
change-type {Γ = Γ} {M = M} Γ⊢M∶A A≡B = subst (λ x → Γ ⊢ M ∶ x) A≡B Γ⊢M∶A
