import SpringerLean.Round1898InterpolationCurvatureBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace SpringerLean

/-- The power kernel whose parameter secant controls the convexity loss
in the real-exponent interpolation. -/
noncomputable def interpolationCurvatureKernel (t k : ℝ) : ℝ :=
  (k - 1) * t ^ (k - 2)

theorem interpolationCurvatureKernel_hasDerivAt
    {t : ℝ} (ht : 0 < t) (k : ℝ) :
    HasDerivAt (interpolationCurvatureKernel t)
      (t ^ (k - 2) * (1 + (k - 1) * Real.log t)) k := by
  have hpow := ((hasDerivAt_id k).sub_const 2).const_rpow ht
  have h := ((hasDerivAt_id k).sub_const 1).mul hpow
  change HasDerivAt (fun x : ℝ => (x - 1) * t ^ (x - 2))
    (t ^ (k - 2) * (1 + (k - 1) * Real.log t)) k
  have hfun : (fun x : ℝ => (x - 1) * t ^ (x - 2)) =
      (fun x : ℝ => x - 1) * (fun x : ℝ => t ^ (x - 2)) := by
    rfl
  rw [hfun]
  convert h using 1 <;> simp only [id_eq] <;> ring

theorem interpolationCurvatureKernel_deriv_hasDerivAt
    {t : ℝ} (ht : 0 < t) (k : ℝ) :
    HasDerivAt (deriv (interpolationCurvatureKernel t))
      (t ^ (k - 2) *
        (2 * Real.log t + (k - 1) * (Real.log t) ^ 2)) k := by
  have hfirst : deriv (interpolationCurvatureKernel t) =
      fun x => t ^ (x - 2) * (1 + (x - 1) * Real.log t) := by
    funext x
    exact (interpolationCurvatureKernel_hasDerivAt ht x).deriv
  rw [hfirst]
  have hpow := ((hasDerivAt_id k).sub_const 2).const_rpow ht
  have hlin := (hasDerivAt_id k).sub_const 1
  have hlin' := (hlin.mul_const (Real.log t)).const_add 1
  have h := hpow.mul hlin'
  change HasDerivAt ((fun x : ℝ => t ^ (x - 2)) *
      (fun x => 1 + (x - 1) * Real.log t)) _ k
  convert h using 1 <;> simp only [id_eq] <;> ring

theorem interpolationCurvatureKernel_second_deriv
    {t : ℝ} (ht : 0 < t) (k : ℝ) :
    deriv (deriv (interpolationCurvatureKernel t)) k =
      t ^ (k - 2) *
        (2 * Real.log t + (k - 1) * (Real.log t) ^ 2) :=
  (interpolationCurvatureKernel_deriv_hasDerivAt ht k).deriv

end SpringerLean

#print axioms SpringerLean.interpolationCurvatureKernel_second_deriv
