import SpringerLean.Round1695ActualKnotTimeFderivFlatAE
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Asymptotics.Basic

open scoped Topology
open Filter Asymptotics

namespace SpringerLean

/-- A Lipschitz real cutoff composed with a function whose real
fderiv vanishes at a point also has zero fderiv there. This is the
chain rule needed at positive-area multiplier knot levels. -/
theorem lipschitz_comp_hasFDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : E → ℝ) (φ : ℝ → ℝ) (x : E) {C : NNReal}
    (ht : HasFDerivAt t (0 : E →L[ℝ] ℝ) x) (hφ : LipschitzWith C φ) :
    HasFDerivAt (fun y => φ (t y)) (0 : E →L[ℝ] ℝ) x := by
  have htLittle :
      (fun h : E => t (x + h) - t x) =o[𝓝 (0 : E)]
        (fun h : E => h) := by
    simpa only [ContinuousLinearMap.zero_apply, sub_zero] using
      (hasFDerivAt_iff_isLittleO_nhds_zero.mp ht)
  have hBig :
      (fun h : E => φ (t (x + h)) - φ (t x)) =O[𝓝 (0 : E)]
        (fun h : E => t (x + h) - t x) := by
    refine (IsBigOWith.of_bound (c := (C : ℝ)) ?_).isBigO
    filter_upwards [] with h
    simpa only [Real.norm_eq_abs, Real.dist_eq] using
      hφ.dist_le_mul (t (x + h)) (t x)
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simpa only [ContinuousLinearMap.zero_apply, sub_zero] using
    hBig.trans_isLittleO htLittle

end SpringerLean

#print axioms SpringerLean.lipschitz_comp_hasFDerivAt_zero
