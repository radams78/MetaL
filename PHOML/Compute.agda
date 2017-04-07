module PHOML.Compute where
open import Data.Empty renaming (⊥ to Empty)
open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.Product hiding (map) renaming (_,_ to _,p_)
open import Data.Sum hiding (map)
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red
open import PHOML.Canon
open import PHOML.Neutral
open import PHOML.Compute.PC public
open import PHOML.Compute.Prp public
open import PHOML.Compute.TermPath public

⊧_∶_ : ∀ {V K} → VExpression V K → Expression V (parent K) → Set
⊧_∶_ {K = -Proof} δ φ = ⊧P δ ∶ φ
⊧_∶_ {K = -Term} M A = ⊧T M ∶ yt A
⊧_∶_ {K = -Path} P (app (-eq A) (M ∷ (N ∷ []))) = ⊧E P ∶ M ≡〈 A 〉 N

⊧rep : ∀ {U V K} {E : VExpression U K} {T} {ρ : Rep U V} → ⊧ E ∶ T → ⊧ E 〈 ρ 〉 ∶ T 〈 ρ 〉
⊧rep {K = -Proof} = ⊧Prep
⊧rep {K = -Term} {T = app (-ty _) []} = ⊧Trep _
⊧rep {K = -Path} {T = app (-eq _) (_ ∷ (_ ∷ []))} = ⊧Erep

not-λλλ-red-CanonΩ : ∀ {V A Q} {Qc : CanonΩ V} → λλλ A Q ↠ decode-CanonΩ Qc → Empty
not-λλλ-red-CanonΩ λQ↠Qc with λλλ-red-ref λQ↠Qc refl
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (var x)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (app*N x x₁ x₂ x₃)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (imp*l x x₁)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {neutral (imp*r x x₁)} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {reffC x} λQ↠Qc | ()
not-λλλ-red-CanonΩ {V} {A} {Q} {univC x x₁ x₂ x₃} λQ↠Qc | ()

not-⊧Pλλλ : ∀ {V d A} {P : Path (extend V pathDom)} {φ} → ⊧P dir d (λλλ A P) ∶ φ → Empty
not-⊧Pλλλ {V} {d} {A} {P} ⊧λAP∶φ with Lemma35e ⊧λAP∶φ
not-⊧Pλλλ {V} {d} {A} {P} _ | δ ,p λP↠canon = not-λλλ-red-CanonΩ {V} {A} {P} {Qc = δ} λP↠canon
