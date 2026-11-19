import SpringerLean.Round1865ArcsineGammaMoment

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate

namespace SpringerLean

theorem slitMap_forward_germ_eq_linear (a : ℂ) :
    exteriorForwardGerm (slitMap a) = fun u : ℂ => a * u := by
  funext u
  by_cases hu : u = 0
  · simp [hu, exteriorForwardGerm_zero]
  · rw [exteriorForwardGerm_punctured _ hu, slitMap]
    field_simp
    <;> ring

theorem actualExteriorRadialTrace_slitMap (a : ℂ) (θ : ℝ) :
    actualExteriorRadialTrace (slitMap a) θ =
      Complex.polarCoord.symm (1, θ) + a * conj (Complex.polarCoord.symm (1, θ)) := by
  rw [actualExteriorRadialTrace, exteriorForwardConjugateRadialTrace,
    slitMap_forward_germ_eq_linear]
  have hd (u : ℂ) : deriv (fun u : ℂ => a * u) u = a := by simp
  simp_rw [hd]
  rw [intervalIntegral.integral_const, polar_radius_eq_mul_unit (1 / 2) θ]
  push_cast
  simp only [map_mul, map_div₀, map_one, map_ofNat, Complex.real_smul]
  push_cast
  ring

theorem actualExteriorRadialTrace_slitMap_one (θ : ℝ) :
    actualExteriorRadialTrace (slitMap 1) θ = ((2 * Real.cos θ : ℝ) : ℂ) := by
  rw [actualExteriorRadialTrace_slitMap]
  apply Complex.ext <;> simp [Complex.polarCoord_symm_apply] <;> ring

theorem integral_center_abs_cos_rpow_eq_two (p : ℝ) (hp : 0 < p) :
    (∫ θ in (-Real.pi)..Real.pi, |Real.cos θ| ^ p) =
      2 * (∫ θ in (0 : ℝ)..Real.pi, |Real.cos θ| ^ p) := by
  let f : ℝ → ℝ := fun θ => |Real.cos θ| ^ p
  have hf : Continuous f := (Real.continuous_rpow_const hp.le).comp (by fun_prop)
  have hneg : (∫ θ in (-Real.pi)..(0 : ℝ), f θ) =
      ∫ θ in (0 : ℝ)..Real.pi, f θ := by
    have hh := intervalIntegral.integral_comp_neg f (a := 0) (b := Real.pi)
    simpa only [neg_zero, f, Real.cos_neg] using hh.symm
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (-Real.pi) 0)
    (hf.intervalIntegrable (μ := volume) 0 Real.pi)
  change (∫ θ in (-Real.pi)..Real.pi, f θ) = _
  rw [← hadd, hneg]
  ring

/-- An actual slit witness for every positive real exponent, with the
boundary representative identified explicitly. -/
theorem actualBoundaryRadialMoment_slitMap_one (p : ℝ) (hp : 0 < p) :
    actualBoundaryRadialMoment (slitMap 1) p = slitRadialMomentConstant p := by
  rw [actualBoundaryRadialMoment]
  simp_rw [actualExteriorRadialTrace_slitMap_one, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (Real.cos _))]
  rw [MeasureTheory.integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi),
    integral_center_abs_cos_rpow_eq_two p hp, integral_abs_cos_rpow_eq_two_half p hp]
  have he : (2 * Real.pi)⁻¹ * ((2 : ℝ) ^ p *
      (2 * (2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p))) =
      (2 : ℝ) ^ (p + 1) / Real.pi *
        (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    field_simp
    <;> ring
  rw [he]
  exact normalized_cosine_half_integral_eq_slit_constant p hp

end SpringerLean

#print axioms SpringerLean.actualBoundaryRadialMoment_slitMap_one
