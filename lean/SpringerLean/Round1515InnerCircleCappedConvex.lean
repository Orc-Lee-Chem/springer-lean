import SpringerLean.Round1514AngularPointwiseCaps
import SpringerLean.Round730ActualInnerConvex

open Set
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The sharpened peak cap applies on the entire actual inner circle,
with the same normalization as its circular convex order. -/
theorem actualHarmonic_inner_circle_capped_convex
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖=1) (h : ℝ)
    (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∀ θ : ℝ,
      (conj ξ*actualHarmonic F (circleMap 0 r θ)).re ≤
        flattenedCosinePoissonAtReal h r) ∧
    (∀ ψ : ℝ → ℝ, ConvexOn ℝ univ ψ →
      Real.circleAverage
        (fun z => ψ ((conj ξ*actualHarmonic F z).re)) 0 r ≤
      Real.circleAverage (fun z : ℂ => ψ (2*z.re)) 0 r) := by
  constructor
  · intro θ
    have hn : ‖circleMap 0 r θ‖ = r := by
      simp [circleMap_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0]
    simpa only [hn] using actualHarmonic_flattened_peak_cap
      F hc ξ hξ h hh0 hhpi hcap (circleMap 0 r θ)
        (by rw [hn]; exact hr0) (by rw [hn]; exact hr1)
  · intro ψ hψ
    exact actualHarmonic_inner_convex_le F hc ξ hξ hr0.le hr1 ψ hψ

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_circle_capped_convex
