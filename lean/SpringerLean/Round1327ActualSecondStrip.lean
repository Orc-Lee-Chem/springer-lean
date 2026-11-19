import SpringerLean.Round1326SecondEndpointRadius
import SpringerLean.Round637RotatedExplicitStrip

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- Any nonzero *actual* omitted endpoint admits the squared-width
parabolic strip on the whole ordinary convex hull.  Apply this to
both endpoints supplied by Round1326; no final deficit precision is
claimed for the second radius. -/
theorem exteriorOmitted_actual_endpoint_rotated_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P : ℂ) (hP : P ∈ exteriorOmitted F) (hP0 : P ≠ 0)
    {r : ℝ} (hr : 1 < r)
    {w : ℂ} (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    let ξ : ℂ := P/(‖P‖ : ℂ)
    let W : ℝ := (exteriorRealRootWidth ‖P‖ r)^2
    (conj ξ*w).im^2 ≤ 4*W*(W+‖P‖-(conj ξ*w).re) ∧
    ‖w‖^2 ≤ ((conj ξ*w).re-2*W)^2+4*W*‖P‖ := by
  dsimp only
  let ξ : ℂ := P/(‖P‖ : ℂ)
  have hnorm : (0 : ℝ) < ‖P‖ := norm_pos_iff.mpr hP0
  have hnorm0 : (‖P‖ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hnorm)
  have hξ : ‖ξ‖ = 1 := by
    dsimp [ξ]
    simp [norm_div, Complex.norm_real, abs_of_pos hnorm, ne_of_gt hnorm]
  have hξP : ξ*(‖P‖ : ℂ)=P := by
    dsimp [ξ]
    field_simp [hnorm0]
  have hP2 : ‖P‖ ≤ 2 := exteriorOmitted_norm_le_two F hc hP
  have hs := exteriorOmitted_convexHull_explicit_rotated_strip
    F hc ξ hξ (R := ‖P‖) (r := r) (norm_nonneg P) hP2
    (by simpa [hξP] using hP) hr hw
  rw [Complex.inv_eq_conj hξ] at hs
  exact hs

end SpringerLean
