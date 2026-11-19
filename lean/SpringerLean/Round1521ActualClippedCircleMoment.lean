import SpringerLean.Round1520ClippedPowerConvex
import SpringerLean.Round730ActualInnerConvex

open Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The actual inner-circle positive-power moment is bounded by the
clipped-tangent test on the ordinary `2r cos` model. This is the exact
functional bridge from a sharpened peak cap plus convex order. -/
theorem actualHarmonic_inner_positivePower_le_clippedModel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hM0 : 0 ≤ flattenedCosinePoissonAtReal h r)
    {m : ℕ} (hm : 1 ≤ m) :
    Real.circleAverage
      (fun z => (max ((conj ξ*actualHarmonic F z).re) 0)^m) 0 r ≤
    Real.circleAverage
      (fun z : ℂ => clippedTangentPower
        (flattenedCosinePoissonAtReal h r) m (2*z.re)) 0 r := by
  let M : ℝ := flattenedCosinePoissonAtReal h r
  have hpoint (z : ℂ) (hz : z ∈ sphere (0:ℂ) |r|) :
      (conj ξ*actualHarmonic F z).re ≤ M := by
    have hzr : ‖z‖=r := by
      simpa only [mem_sphere,dist_zero_right,abs_of_pos hr0] using hz
    simpa only [hzr] using (actualHarmonic_flattened_peak_cap
      F hc ξ hξ h hh0 hhpi hcap z
      (by rw [hzr]; exact hr0) (by rw [hzr]; exact hr1))
  calc
    Real.circleAverage
        (fun z => (max ((conj ξ*actualHarmonic F z).re) 0)^m) 0 r =
      Real.circleAverage
        (fun z => clippedTangentPower M m
          ((conj ξ*actualHarmonic F z).re)) 0 r := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        exact (clippedTangentPower_eq_positivePart_pow (hpoint z hz) m).symm
    _ ≤ Real.circleAverage
        (fun z : ℂ => clippedTangentPower M m (2*z.re)) 0 r :=
      actualHarmonic_inner_convex_le F hc ξ hξ hr0.le hr1
        (clippedTangentPower M m) (clippedTangentPower_convexOn hM0 hm)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_positivePower_le_clippedModel
