import SpringerLean.Round16Potential

namespace SpringerLean

/-- A vertical-line logarithmic kernel in real coordinates. This pointwise
formula remains valid when the line passes through the target, since Lean's
real logarithm takes the value zero at zero on both sides. -/
theorem vertical_log_norm_eq_half_log_squares
    (a y : ℝ) (w : ℂ) :
    Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) - w‖ =
      (1 / 2 : ℝ) * Real.log ((a - w.re) ^ 2 + (y - w.im) ^ 2) := by
  have hsq : ‖((a : ℂ) + (y : ℂ) * Complex.I) - w‖ ^ 2 =
      (a - w.re) ^ 2 + (y - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im]
    ring
  calc
    _ = (1 / 2 : ℝ) * Real.log (‖((a : ℂ) + (y : ℂ) * Complex.I) - w‖ ^ 2) := by
      rw [Real.log_pow]
      ring
    _ = _ := by rw [hsq]

end SpringerLean
