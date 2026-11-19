import SpringerLean.Round1610RadialFieldCoordinates

namespace SpringerLean

private theorem source_decompose (z : ℂ) :
    z = z.re • (1:ℂ) + z.im • Complex.I := by
  apply Complex.ext <;> simp

/-- The radial derivative is the weighted sum of Cartesian derivatives. -/
theorem fderiv_radial_cartesian
    (a : ℂ → ℝ) (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℝ a z) (z/‖z‖) =
      (z.re/‖z‖)*(fderiv ℝ a z) (1:ℂ) +
      (z.im/‖z‖)*(fderiv ℝ a z) Complex.I := by
  have hn : (‖z‖:ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  have hrepr : z / (‖z‖:ℂ) =
      (z.re/‖z‖) • (1:ℂ) + (z.im/‖z‖) • Complex.I := by
    rw [source_decompose z]
    simp [div_eq_mul_inv, Complex.real_smul, add_mul,
      mul_assoc, mul_comm]
  rw [hrepr, map_add, map_smul, map_smul]
  simp

/-- Divergence of a scalar field times the Euclidean radial unit vector.
The scalar field may contain the actual filling, phase and multiplier. -/
theorem radialFlux_divergence_product_rule
    (a : ℂ → ℝ) (z : ℂ)
    (ha : DifferentiableAt ℝ a z) (hz : z ≠ 0) :
    (fderiv ℝ (fun w : ℂ => (a w*w.re)/‖w‖) z) (1:ℂ) +
    (fderiv ℝ (fun w : ℂ => (a w*w.im)/‖w‖) z) Complex.I =
      a z/‖z‖ + (fderiv ℝ a z) (z/‖z‖) := by
  let r : ℂ → ℝ := fun w => ‖w‖
  let ax : ℂ → ℝ := fun w => a w*w.re
  let ay : ℂ → ℝ := fun w => a w*w.im
  have hr : DifferentiableAt ℝ r z := source_radius_differentiableAt hz
  have hn : r z ≠ 0 := norm_ne_zero_iff.mpr hz
  have hrex : DifferentiableAt ℝ (fun w : ℂ => w.re) z :=
    Complex.reCLM.differentiableAt
  have hrey : DifferentiableAt ℝ (fun w : ℂ => w.im) z :=
    Complex.imCLM.differentiableAt
  have hax : DifferentiableAt ℝ ax z := ha.mul hrex
  have hay : DifferentiableAt ℝ ay z := ha.mul hrey
  have hx := fderiv_ratio_apply_of_denominator_ne_zero
    ax r z (1:ℂ) hax hr hn
  have hy := fderiv_ratio_apply_of_denominator_ne_zero
    ay r z Complex.I hay hr hn
  have haxprod := congrArg (fun L : ℂ →L[ℝ] ℝ => L (1:ℂ))
    (fderiv_fun_mul ha hrex)
  have hayprod := congrArg (fun L : ℂ →L[ℝ] ℝ => L Complex.I)
    (fderiv_fun_mul ha hrey)
  simp only [add_apply, smul_apply, smul_eq_mul] at haxprod hayprod
  obtain ⟨hre1, _⟩ := source_re_fderiv_coordinates z
  obtain ⟨_, himI⟩ := source_im_fderiv_coordinates z
  rw [hre1] at haxprod
  rw [himI] at hayprod
  have hrad := source_radius_fderiv_radial hz
  have hcart := fderiv_radial_cartesian r z hz
  have hrad_cart :
      z.re*(fderiv ℝ r z) (1:ℂ) +
      z.im*(fderiv ℝ r z) Complex.I = r z := by
    rw [hcart] at hrad
    dsimp only [r] at hrad ⊢
    field_simp at hrad
    nlinarith [hrad]
  have hada := fderiv_radial_cartesian a z hz
  dsimp only [ax, ay, r] at hx hy haxprod hayprod hrad_cart
  have hnorm : (‖z‖:ℝ) ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [hx, hy, haxprod, hayprod, hada]
  field_simp
  have hmul := congrArg (fun v : ℝ => a z * v) hrad_cart
  nlinarith [hmul]

end SpringerLean

#print axioms SpringerLean.fderiv_radial_cartesian
#print axioms SpringerLean.radialFlux_divergence_product_rule
