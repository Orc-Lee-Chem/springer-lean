import SpringerLean.Round1608ActualMultiplierTimeRegularity

open Filter
open scoped Topology

namespace SpringerLean

/-- Quotient derivative derived from the local identity `(a/y)*y=a`.
This form keeps the numerator's derivative explicit and avoids a
separate inverse-norm derivative formula. -/
theorem fderiv_ratio_apply_of_denominator_ne_zero
    (a y : ℂ → ℝ) (z u : ℂ)
    (ha : DifferentiableAt ℝ a z)
    (hy : DifferentiableAt ℝ y z) (hy0 : y z ≠ 0) :
    (fderiv ℝ (fun w => a w/y w) z) u =
      ((fderiv ℝ a z) u - (a z/y z)*(fderiv ℝ y z) u)/y z := by
  let t : ℂ → ℝ := fun w => a w/y w
  have ht : DifferentiableAt ℝ t z := by
    change DifferentiableAt ℝ (fun w => a w*(y w)⁻¹) z
    exact ha.mul (hy.inv hy0)
  have hlocal : (fun w => t w*y w) =ᶠ[𝓝 z] a := by
    filter_upwards [hy.continuousAt.eventually_ne hy0] with w hw
    dsimp [t]
    exact div_mul_cancel₀ (a w) hw
  have hprod := congrArg (fun L : ℂ →L[ℝ] ℝ => L u)
    (fderiv_fun_mul ht hy)
  rw [hlocal.fderiv_eq] at hprod
  simp only [add_apply, smul_apply, smul_eq_mul] at hprod
  dsimp only [t] at hprod
  apply (eq_div_iff hy0).mpr
  nlinarith [hprod]

/-- Exact directional derivative of the actual multiplier time. -/
theorem actualHarmonicMultiplierTime_fderiv
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) (hH : actualHarmonic F z ≠ 0)
    (u : ℂ) :
    (fderiv ℝ (actualHarmonicMultiplierTime F k) z) u =
      -((k:ℝ)*(fderiv ℝ (fun w : ℂ => ‖w‖) z) u +
        (actualHarmonicMultiplierTime F k z)*
          (fderiv ℝ (fun w : ℂ => ‖actualHarmonic F w‖) z) u) /
        ‖actualHarmonic F z‖ := by
  let a : ℂ → ℝ := fun w => (k:ℝ)*(1-‖w‖)
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  have hr := source_radius_differentiableAt hz0
  have hy := actualHarmonic_norm_differentiableAt F hc hz hH
  have ha : DifferentiableAt ℝ a z :=
    ((differentiableAt_const (x := z) (1:ℝ)).sub hr).const_mul (k:ℝ)
  have hy0 : y z ≠ 0 := norm_ne_zero_iff.mpr hH
  have hratio := fderiv_ratio_apply_of_denominator_ne_zero a y z u ha hy hy0
  have hnum : (fderiv ℝ a z) u =
      -(k:ℝ)*(fderiv ℝ (fun w : ℂ => ‖w‖) z) u := by
    dsimp only [a]
    rw [fderiv_real_const_mul_apply]
    have hsub := congrArg (fun L : ℂ →L[ℝ] ℝ => L u)
      (fderiv_fun_sub (differentiableAt_const (x := z) (1:ℝ)) hr)
    simp at hsub
    rw [hsub]
    ring
  change (fderiv ℝ (fun w => a w/y w) z) u = _
  rw [hratio, hnum]
  dsimp only [a, y, actualHarmonicMultiplierTime]
  ring

end SpringerLean

#print axioms SpringerLean.fderiv_ratio_apply_of_denominator_ne_zero
#print axioms SpringerLean.actualHarmonicMultiplierTime_fderiv
