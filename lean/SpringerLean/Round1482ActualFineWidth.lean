import SpringerLean.Round1481ActualLogDeficits
import SpringerLean.Round652SmallWidthEstimate
import SpringerLean.Round1327ActualSecondStrip

open scoped ComplexConjugate

namespace SpringerLean

/-- Once the actual normalized endpoint deficit is below `3/20`,
the earlier exact `0.31914` root-width theorem supplies the simpler
one-third width for the entire ordinary convex hull. -/
theorem exteriorOmitted_actualEndpoint_fine_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd0 : 0 < 2 - ‖P‖)
    (hdef : ((2*k-1 : ℕ) : ℝ) * (2 - ‖P‖) < 3/20)
    (w : ℂ) (hw : w ∈ convexHull ℝ (exteriorOmitted F)) :
    let ξ : ℂ := P / (‖P‖ : ℂ)
    let r : ℝ := 1 + (2/25:ℝ)*Real.sqrt (2 - ‖P‖)
    let W : ℝ := (exteriorRealRootWidth ‖P‖ r)^2
    W < (1/3 : ℝ) * (2 - ‖P‖) * Real.log (2 / (2 - ‖P‖)) ∧
    (conj ξ*w).im^2 ≤ 4*W*(W+‖P‖-(conj ξ*w).re) ∧
    ‖w‖^2 ≤ ((conj ξ*w).re-2*W)^2+4*W*‖P‖ := by
  let d : ℝ := 2 - ‖P‖
  let L : ℝ := Real.log (2/d)
  have hnNat : 1501 ≤ 2*k-1 := by omega
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by exact_mod_cast hnNat
  have hdn : d ≤ (1/5000 : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hn hd0.le
    dsimp only [d]
    nlinarith
  have hnorm : 0 < ‖P‖ := by dsimp [d] at hdn; linarith
  have hP0 : P ≠ 0 := norm_pos_iff.mp hnorm
  have hr : 1 < 1 + (2/25:ℝ)*Real.sqrt d := by
    have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    nlinarith
  have hstrip := exteriorOmitted_actual_endpoint_rotated_strip
    F hc P hP hP0 hr hw
  have hW : (exteriorRealRootWidth ‖P‖
      (1+(2/25:ℝ)*Real.sqrt d))^2 <
      (31914/100000:ℝ)*d*L := by
    have hh := smallWidth_exact_width_sq_lt hd0 hdn
    have heq : (2 : ℝ)-d=‖P‖ := by dsimp [d]; ring
    rw [heq] at hh
    exact hh
  have hL0 : 0 < L := by
    have harg : (1:ℝ)<2/d := by
      apply (lt_div_iff₀ hd0).2
      linarith
    exact Real.log_pos harg
  have hmul := mul_lt_mul_of_pos_right
    (by norm_num : (31914/100000:ℝ)<1/3)
    (mul_pos hd0 hL0)
  have hWthird : (exteriorRealRootWidth ‖P‖
      (1+(2/25:ℝ)*Real.sqrt d))^2 < (1/3:ℝ)*d*L := by
    nlinarith [hW,hmul]
  dsimp only
  exact ⟨hWthird,hstrip.1,hstrip.2⟩

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_fine_strip
