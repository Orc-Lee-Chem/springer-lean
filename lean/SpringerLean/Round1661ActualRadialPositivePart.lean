import SpringerLean.Round1659InverseDriftScalarProjection

namespace SpringerLean

/-- The radial geometric term in the multiplier can be charged to the
positive part of f, including negative values of a provisional slope. -/
theorem actualHarmonic_radial_multiplier_positivePart_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (f : ℝ) :
    (‖actualHarmonic F z‖ / ‖z‖) * f ≤ 2 * max 0 f := by
  have hr : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  have hy : (0:ℝ) ≤ ‖actualHarmonic F z‖ := norm_nonneg _
  have hbound := actualHarmonic_norm_le_two_norm F hc hz
  have hratio0 : 0 ≤ ‖actualHarmonic F z‖ / ‖z‖ := div_nonneg hy (le_of_lt hr)
  have hratio2 : ‖actualHarmonic F z‖ / ‖z‖ ≤ 2 := by
    apply (div_le_iff₀ hr).2
    nlinarith
  by_cases hf : 0 ≤ f
  · rw [max_eq_right hf]
    exact mul_le_mul_of_nonneg_right hratio2 hf
  · have hf0 : f ≤ 0 := le_of_lt (lt_of_not_ge hf)
    rw [max_eq_left hf0]
    have := mul_nonpos_of_nonneg_of_nonpos hratio0 hf0
    nlinarith

end SpringerLean

#print axioms SpringerLean.actualHarmonic_radial_multiplier_positivePart_le
