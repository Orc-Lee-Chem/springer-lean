import SpringerLean.Round1404MediumWidthEstimate
import SpringerLean.Round1401ActualSelectedDeficits
import SpringerLean.Round1327ActualSecondStrip

open scoped ComplexConjugate

namespace SpringerLean

/-- The width estimate now holds for an actual omitted endpoint throughout
the whole positive localized range `n d < 1`, and the corresponding strip
controls every point of the ordinary convex hull. -/
theorem exteriorOmitted_actualEndpoint_localized_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd0 : 0 < 2 - ‖P‖)
    (hdef : ((2*k-1 : ℕ) : ℝ) * (2 - ‖P‖) < 1)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    let ξ : ℂ := P / (‖P‖ : ℂ)
    let r : ℝ := 1 + Real.sqrt (2 - ‖P‖)/10
    let W : ℝ := (exteriorRealRootWidth ‖P‖ r)^2
    W < (34/100 : ℝ) * (2 - ‖P‖) * Real.log (2 / (2 - ‖P‖)) ∧
    (conj ξ*w).im^2 ≤ 4*W*(W+‖P‖-(conj ξ*w).re) ∧
    ‖w‖^2 ≤ ((conj ξ*w).re-2*W)^2+4*W*‖P‖ := by
  let d : ℝ := 2 - ‖P‖
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by exact_mod_cast hnNat
  have hdn : d ≤ (1/1501 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hn hd0.le
    dsimp only [d]
    nlinarith
  have hnorm : 0 < ‖P‖ := by dsimp [d] at hdn; linarith
  have hP0 : P ≠ 0 := norm_pos_iff.mp hnorm
  have hr : 1 < 1 + Real.sqrt d/10 := by
    have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    nlinarith
  have hstrip := exteriorOmitted_actual_endpoint_rotated_strip
    F hc P hP hP0 hr hw
  have hW : (exteriorRealRootWidth ‖P‖ (1+Real.sqrt d/10))^2 <
      (34/100 : ℝ)*d*Real.log (2/d) := by
    have hh := mediumWidth_exact_width_sq_lt hd0 hdn
    have heq : (2 : ℝ)-d=‖P‖ := by dsimp [d]; ring
    rw [heq] at hh
    exact hh
  dsimp only
  exact ⟨hW,hstrip.1,hstrip.2⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_localized_strip
