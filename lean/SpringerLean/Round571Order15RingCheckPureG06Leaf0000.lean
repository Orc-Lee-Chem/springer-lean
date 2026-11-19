import SpringerLean.Round735WholeOrderedScaled
import SpringerLean.Round570Order15RingDataG06L00
import SpringerLean.Round622PureGramIdentity
import SpringerLean.Round701ClearedHybridSoundness

namespace SpringerLean
open RatPolyCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem order15RingTreeG06L00_identity (env : (Bool × Nat) → ℂ) :
    order15RingTreeG06L00Block.polynomial.eval env =
      (order15RingTreeG06L00Block.certificate.cachedBody grunskyCoeffCache16).eval env :=
  WholeOrderedScaled.check_sound env coeffExprVariableOrder 2329089562800 _ _ (by decide +kernel)

end SpringerLean
#print axioms SpringerLean.order15RingTreeG06L00_identity
