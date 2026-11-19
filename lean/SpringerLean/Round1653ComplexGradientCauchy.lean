import SpringerLean.Round1652ActualAntiholomorphicCost

namespace SpringerLean

/-- The two-dimensional Cauchy inequality in the exact gradient
normalization used by actualHarmonicPhaseEnergy. -/
theorem complex_dot_abs_le_gradient_sqrt
    (Q : ℂ) (ux uy : ℝ) :
    |Q.re*ux+Q.im*uy| ≤
      ‖Q‖*Real.sqrt (ux^2+uy^2) := by
  let p := Real.sqrt (ux^2+uy^2)
  have hsq : 0 ≤ ux^2+uy^2 := by positivity
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hnorm : ‖Q‖^2 = Q.re^2+Q.im^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hcs : (Q.re*ux+Q.im*uy)^2 ≤
      (Q.re^2+Q.im^2)*(ux^2+uy^2) := by
    nlinarith [sq_nonneg (Q.re*uy-Q.im*ux)]
  have hsq' : |Q.re*ux+Q.im*uy|^2 ≤ (‖Q‖*p)^2 := by
    rw [sq_abs,mul_pow,Real.sq_sqrt hsq,hnorm]
    exact hcs
  exact (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg (norm_nonneg Q) hp)).mp hsq'

end SpringerLean

#print axioms SpringerLean.complex_dot_abs_le_gradient_sqrt
