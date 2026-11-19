import SpringerLean.Round1653ComplexGradientCauchy

open scoped ComplexConjugate

namespace SpringerLean

/-- The residual actual drift in the combined flux costs exactly
|u| p, with no extra factor from planar coordinates. -/
theorem inverseConjugate_drift_abs_le
    (H : ℂ) (U ux uy : ℝ) :
    |U*(((conj H)⁻¹).re*ux+((conj H)⁻¹).im*uy)| ≤
      |U/‖H‖| * Real.sqrt (ux^2+uy^2) := by
  let Q := (conj H)⁻¹
  let p := Real.sqrt (ux^2+uy^2)
  have hdot := complex_dot_abs_le_gradient_sqrt Q ux uy
  have hQnorm : ‖Q‖ = 1/‖H‖ := by
    simp [Q, norm_inv]
  calc
    |U*(Q.re*ux+Q.im*uy)| = |U| * |Q.re*ux+Q.im*uy| :=
      abs_mul _ _
    _ ≤ |U| * (‖Q‖*p) :=
      mul_le_mul_of_nonneg_left hdot (abs_nonneg U)
    _ = |U/‖H‖| * p := by
      rw [hQnorm, abs_div, abs_of_nonneg (norm_nonneg H)]
      ring

end SpringerLean

#print axioms SpringerLean.inverseConjugate_drift_abs_le
