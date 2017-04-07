--Parallel reduction
module PHOML.Red.PRed where
open import Prelims
open import PHOML.Grammar
open import PHOML.Red.RTRed
open import PHOML.Red.POSR

_▷*_ : ∀ {V K} → VExpression V K → VExpression V K → Set
_▷*_ = RTClose _▷_

sub-↠-▷* : ∀ {V K} {E F : VExpression V K} → E ↠ F → E ▷* F
sub-↠-▷* = monoRT sub-⇒-▷

sub-▷*-↠ : ∀ {V K} {E F : VExpression V K} → E ▷* F → E ↠ F
sub-▷*-↠ (inc E▷F) = sub-▷-↠ E▷F
sub-▷*-↠ ref = ref
sub-▷*-↠ (trans E▷*F F▷*G) = trans (sub-▷*-↠ E▷*F) (sub-▷*-↠ F▷*G)

diamond-▷-▷* : ∀ {V K} {E F G : VExpression V K} → E ▷ F → E ▷* G →
  Common-Reduct _▷*_ _▷_ F G
diamond-▷-▷* E▷F (inc E▷G) =
  let cr H F▷H G▷H = diamond-▷ E▷F E▷G in cr H (inc F▷H) G▷H
diamond-▷-▷* E▷F ref = cr _ ref E▷F
diamond-▷-▷* E▷F (trans E▷*G G▷*G') =
  let cr H F▷*H G▷H = diamond-▷-▷* E▷F E▷*G in
  let cr H' H▷*H' G'▷H' = diamond-▷-▷* G▷H G▷*G' in
  cr H' (trans F▷*H H▷*H') G'▷H'

diamond-▷* :  ∀ {V K} {E F G : VExpression V K} → E ▷* F → E ▷* G →
  Common-Reduct _▷*_ _▷*_ F G
diamond-▷* (inc E▷F) E▷*G =
  let cr H F▷*H G▷H = diamond-▷-▷* E▷F E▷*G in 
  cr H F▷*H (inc G▷H)
diamond-▷* ref E▷*G = cr _ E▷*G ref
diamond-▷* (trans E▷*F F▷*F') E▷*G =
  let cr H F▷*H G▷*H = diamond-▷* E▷*F E▷*G in
  let cr H' F'▷*H' H▷*H' = diamond-▷* F▷*F' F▷*H in
  cr H' F'▷*H' (trans G▷*H H▷*H')
