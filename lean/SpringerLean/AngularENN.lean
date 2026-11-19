import SpringerLean.PolarArea

open MeasureTheory

namespace SpringerLean

/-- The fixed-circle finite Bessel bound in the nonnegative integral form
used by Tonelli's polar-coordinate formula. -/
theorem exteriorDerivativeCircle_finite_lintegral_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    ENNReal.ofReal
      ((2 * Real.pi) *
        (1 + ∑ j ∈ Finset.Icc 1 N,
          (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
            (ρ⁻¹) ^ (2 * j + 2))) ≤
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal
          (‖deriv F (exteriorCirclePoint ρ
            (θ : AddCircle (2 * Real.pi)))‖ ^ 2) ∂volume := by
  let e : ℝ → ℝ := fun θ =>
    ‖deriv F (exteriorCirclePoint ρ
      (θ : AddCircle (2 * Real.pi)))‖ ^ 2
  have hcoe : Continuous (fun θ : ℝ =>
      (θ : AddCircle (2 * Real.pi))) := by fun_prop
  have hecont : Continuous e :=
    (((actualCircleDerivative_continuous F hc hρ).comp hcoe).norm.pow 2)
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_nonneg]
  have hπpos : 0 < 2 * Real.pi := by positivity
  have hint : IntegrableOn e (Set.Ioo (-Real.pi) Real.pi) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hπ).mp
      (hecont.intervalIntegrable (-Real.pi) Real.pi)
  have hlin :
      ENNReal.ofReal
        (∫ θ in Set.Ioo (-Real.pi) Real.pi, e θ ∂volume) =
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal (e θ) ∂volume := by
    apply ofReal_integral_eq_lintegral_ofReal hint
    filter_upwards [] with θ
    exact sq_nonneg _
  have hcircle := exteriorDerivativeCircle_interval_finite_energy_le F hc hρ N
  have hscaled :
      (2 * Real.pi) *
        (1 + ∑ j ∈ Finset.Icc 1 N,
          (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
            (ρ⁻¹) ^ (2 * j + 2)) ≤
        ∫ θ in -Real.pi..Real.pi, e θ := by
    have h := mul_le_mul_of_nonneg_left hcircle hπpos.le
    convert h using 1
    field_simp
    rfl
  have hset :
      (∫ θ in -Real.pi..Real.pi, e θ) =
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, e θ ∂volume := by
    rw [intervalIntegral.integral_of_le hπ,
      integral_Ioc_eq_integral_Ioo]
  rw [hset] at hscaled
  exact (ENNReal.ofReal_le_ofReal hscaled).trans_eq hlin

end SpringerLean
