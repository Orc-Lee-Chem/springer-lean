import SpringerLean.Round1609MultiplierTimeDerivative
import Mathlib.Analysis.Calculus.FDeriv.Norm

namespace SpringerLean

/-- The derivative of the Euclidean radius in the radial direction. -/
theorem source_radius_fderiv_radial
    {z : ℂ} (hz : z ≠ 0) :
    (fderiv ℝ (fun w : ℂ => ‖w‖) z) (z/‖z‖) = 1 := by
  have hr := source_radius_differentiableAt hz
  have hself := DifferentiableAt.fderiv_norm_self hr
  have hn : (‖z‖:ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hrepr : z / (‖z‖:ℂ) = (‖z‖:ℝ)⁻¹ • z := by
    simp [div_eq_mul_inv, Complex.real_smul, mul_comm]
  rw [hrepr]
  rw [map_smul, hself]
  simp [hn]

/-- The real coordinate derivative, in the two Cartesian directions. -/
theorem source_re_fderiv_coordinates (z : ℂ) :
    (fderiv ℝ (fun w : ℂ => w.re) z) (1:ℂ) = 1 ∧
    (fderiv ℝ (fun w : ℂ => w.re) z) Complex.I = 0 := by
  have h : fderiv ℝ (fun w : ℂ => w.re) z = Complex.reCLM := by
    exact Complex.reCLM.fderiv
  rw [h]
  simp

/-- The imaginary coordinate derivative, in the two Cartesian directions. -/
theorem source_im_fderiv_coordinates (z : ℂ) :
    (fderiv ℝ (fun w : ℂ => w.im) z) (1:ℂ) = 0 ∧
    (fderiv ℝ (fun w : ℂ => w.im) z) Complex.I = 1 := by
  have h : fderiv ℝ (fun w : ℂ => w.im) z = Complex.imCLM := by
    exact Complex.imCLM.fderiv
  rw [h]
  simp

end SpringerLean

#print axioms SpringerLean.source_radius_fderiv_radial
#print axioms SpringerLean.source_re_fderiv_coordinates
#print axioms SpringerLean.source_im_fderiv_coordinates
