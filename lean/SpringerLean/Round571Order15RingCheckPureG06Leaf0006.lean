import SpringerLean.Round735WholeOrderedScaled
import SpringerLean.Round570Order15RingDataG06L06
import SpringerLean.Round571Order15RingCheckPureG06Leaf0005
import SpringerLean.Round622PureGramIdentity
import SpringerLean.Round701ClearedHybridSoundness

namespace SpringerLean
open RatPolyCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem order15RingTreeG06L06_identity (env : (Bool × Nat) → ℂ) :
    order15RingTreeG06L06Block.polynomial.eval env =
      (order15RingTreeG06L06Block.certificate.cachedBody grunskyCoeffCache16).eval env :=
  WholeOrderedScaled.check_sound env coeffExprVariableOrder 2329089562800 _ _ (by decide +kernel)

end SpringerLean
#print axioms SpringerLean.order15RingTreeG06L06_identity
