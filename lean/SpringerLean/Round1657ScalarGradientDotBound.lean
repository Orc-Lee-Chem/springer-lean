import SpringerLean.Round1656RadialScalarDerivativeBound

namespace SpringerLean

/-- The scalar modulus gradient paired with the phase gradient costs
exactly the operator norm of d|H| times the phase-gradient length. -/
theorem scalar_fderiv_dot_gradient_abs_le
    (f : ℂ → ℝ) (z : ℂ) (ux uy : ℝ) :
    |(fderiv ℝ f z) (1:ℂ)*ux +
      (fderiv ℝ f z) Complex.I*uy| ≤
      ‖fderiv ℝ f z‖ * Real.sqrt (ux^2+uy^2) := by
  let v : ℂ := ⟨ux,uy⟩
  have hrepr : v = ux • (1:ℂ)+uy • Complex.I := by
    apply Complex.ext <;> simp [v]
  have hL : (fderiv ℝ f z) v =
      (fderiv ℝ f z) (1:ℂ)*ux +
      (fderiv ℝ f z) Complex.I*uy := by
    rw [hrepr, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    ring
  have hvnorm : ‖v‖ = Real.sqrt (ux^2+uy^2) := by
    simp [v, Complex.norm_def, Complex.normSq_apply]
    ring
  have hbound := (fderiv ℝ f z).le_opNorm v
  rw [hL,hvnorm] at hbound
  simpa only [Real.norm_eq_abs] using hbound

end SpringerLean

#print axioms SpringerLean.scalar_fderiv_dot_gradient_abs_le
