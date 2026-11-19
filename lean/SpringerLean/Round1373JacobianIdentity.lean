import SpringerLean.Round1372InverseProfileBranches
import SpringerLean.Round1340CoarseJacobianScalar

namespace SpringerLean

/-- Algebraic identity behind the active arcsine-density substitution
`s=e+5e²`: the denominator in the exact Jacobian is the same one
bounded in Round1340. -/
theorem coarseJacobian_density_sq_identity
    {e : ℝ} (he0 : 0 < e) (heδ : e ≤ 1/20) :
    e*(4-e)/((e+5*e^2)*(4-e-5*e^2)) =
      1/((1+5*e)*(1-5*e^2/(4-e))) := by
  have h4e : 0 < 4-e := by linarith
  have h1e : 0 < 1+5*e := by linarith
  have h4s : 0 < 4-e-5*e^2 := by
    have he2 : e^2 ≤ (1/20 : ℝ)^2 :=
      (sq_le_sq₀ he0.le (by norm_num)).mpr heδ
    nlinarith
  have hs : 0 < e+5*e^2 := by nlinarith [sq_nonneg e]
  field_simp

theorem coarseJacobian_density_identity
    {e : ℝ} (he0 : 0 < e) (heδ : e ≤ 1/20) :
    Real.sqrt (e*(4-e)/((e+5*e^2)*(4-e-5*e^2))) =
      1/Real.sqrt ((1+5*e)*(1-5*e^2/(4-e))) := by
  rw [coarseJacobian_density_sq_identity he0 heδ]
  simpa only [one_div] using
    (Real.sqrt_inv ((1+5*e)*(1-5*e^2/(4-e))))

end SpringerLean

#print axioms SpringerLean.coarseJacobian_density_sq_identity
#print axioms SpringerLean.coarseJacobian_density_identity
