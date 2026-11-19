import SpringerLean.Round1719EnergyMultipliersBounded
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Asymptotics
open scoped Topology

namespace SpringerLean

/-- A vector field that vanishes to order strictly greater than one
at a point has zero real fderiv there. This is the scalar criterion
used for the actual flux across an H-zero. -/
theorem hasFDerivAt_zero_of_power_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (J : E → F) (x : E) (n : ℕ) (hn : 1 < n)
    (hJ : J x = 0) (C : ℝ)
    (hbound : ∀ᶠ z in 𝓝 x,
      ‖J z‖ ≤ C * ‖z - x‖^n) :
    HasFDerivAt J (0 : E →L[ℝ] F) x := by
  have hBig : J =O[𝓝 x] (fun z => ‖z - x‖^n) := by
    apply (IsBigOWith.of_bound (c := C) ?_).isBigO
    filter_upwards [hbound] with z hz
    simpa using hz
  have hSmall : J =o[𝓝 x] (fun z => z - x) :=
    hBig.trans_isLittleO (isLittleO_pow_sub_sub x hn)
  rw [hasFDerivAt_iff_isLittleO]
  simpa [hJ] using hSmall

end SpringerLean

#print axioms SpringerLean.hasFDerivAt_zero_of_power_bound
