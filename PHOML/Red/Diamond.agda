module PHOML.Red.Diamond where
open import Prelims
open import PHOML.Grammar
open import PHOML.PathSub
open import PHOML.Red.Base
open import PHOML.Red.RRed
open import PHOML.Red.RTRed
open import PHOML.Red.POSR
open import PHOML.Red.PRed

diamond : ∀ {V K} {E F G : VExpression V K} → E ↠ F → E ↠ G → Common-Reduct _↠_ _↠_ F G
diamond E↠F E↠G = 
  let cr H F▷*H G▷*H = diamond-▷* (sub-↠-▷* E↠F) (sub-↠-▷* E↠G) in 
  cr H (sub-▷*-↠ F▷*H) (sub-▷*-↠ G▷*H)
