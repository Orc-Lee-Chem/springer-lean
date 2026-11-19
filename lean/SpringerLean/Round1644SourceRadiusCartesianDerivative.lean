import SpringerLean.Round1643ActualFluxDriftCancellation

namespace SpringerLean

/-- Cartesian derivatives of the source radius, away from the origin. -/
theorem source_radius_fderiv_coordinates
    {z : ℂ} (hz : z ≠ 0) :
    (fderiv ℝ (fun w : ℂ => ‖w‖) z) (1:ℂ) = z.re/‖z‖ ∧
    (fderiv ℝ (fun w : ℂ => ‖w‖) z) Complex.I = z.im/‖z‖ := by
  let r : ℂ → ℝ := fun w => ‖w‖
  let x : ℂ → ℝ := fun w => w.re
  let y : ℂ → ℝ := fun w => w.im
  have hr := source_radius_differentiableAt hz
  have hx : DifferentiableAt ℝ x z := Complex.reCLM.differentiableAt
  have hy : DifferentiableAt ℝ y z := Complex.imCLM.differentiableAt
  have hid : (fun w : ℂ => (r w)^2) =
      fun w => (x w)^2+(y w)^2 := by
    funext w
    simp [r, x, y, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring
  have hdl := (hr.hasFDerivAt.pow 2).fderiv
  have hdr := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ))
    (fderiv_fun_add (hx.pow 2) (hy.pow 2))
  have hdi := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I)
    (fderiv_fun_add (hx.pow 2) (hy.pow 2))
  have hpx := (hx.hasFDerivAt.pow 2).fderiv
  have hpy := (hy.hasFDerivAt.pow 2).fderiv
  have hsqx := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ)) hpx
  have hsqy := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hpy
  have hsqxi := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I) hpx
  have hsqyr := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ)) hpy
  change (fderiv ℝ (x^2) z) (1:ℂ) = _ at hsqx
  change (fderiv ℝ (y^2) z) Complex.I = _ at hsqy
  change (fderiv ℝ (x^2) z) Complex.I = _ at hsqxi
  change (fderiv ℝ (y^2) z) (1:ℂ) = _ at hsqyr
  simp only [smul_apply, smul_eq_mul, add_apply] at *
  rw [hsqx, hsqyr] at hdr
  rw [hsqxi, hsqy] at hdi
  have hxcoords := source_re_fderiv_coordinates z
  have hycoords := source_im_fderiv_coordinates z
  rw [hxcoords.1, hycoords.1] at hdr
  rw [hxcoords.2, hycoords.2] at hdi
  change (fderiv ℝ (fun w => x w ^ 2 + y w ^ 2) z) (1:ℂ) = _ at hdr
  change (fderiv ℝ (fun w => x w ^ 2 + y w ^ 2) z) Complex.I = _ at hdi
  have hnormx := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ))
    (congrArg (fderiv ℝ · z) hid)
  have hnormy := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I)
    (congrArg (fderiv ℝ · z) hid)
  rw [hdl] at hnormx hnormy
  simp only [smul_apply, smul_eq_mul] at hnormx hnormy
  rw [hdr] at hnormx
  rw [hdi] at hnormy
  norm_num at hnormx hnormy
  have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  constructor <;> apply (eq_div_iff (ne_of_gt hrpos)).mpr <;>
    dsimp only [r, x, y] at * <;> nlinarith

end SpringerLean

#print axioms SpringerLean.source_radius_fderiv_coordinates
