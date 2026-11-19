import SpringerLean.RadialFinite

open MeasureTheory AddCircle

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

/-- Algebraic match between the integrated radial energy and the Fourier
mode sum at each positive radius. -/
theorem exteriorRadialFiniteEnergy_eq_modes
    (F : ℂ → ℂ) {ρ : ℝ} (hρ : 0 < ρ) (N : ℕ) :
    2 * ρ + ∑ j ∈ Finset.Icc 1 N,
      ‖exteriorForwardCoeff F j‖ ^ 2 *
        (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)) =
      2 * ρ * (1 + ∑ j ∈ Finset.Icc 1 N,
        (j : ℝ) ^ 2 * ‖exteriorForwardCoeff F j‖ ^ 2 *
          (ρ⁻¹) ^ (2 * j + 2)) := by
  rw [mul_add, mul_one, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have hpow : ρ * (ρ⁻¹) ^ (2 * j + 2) =
      (ρ⁻¹) ^ (2 * j + 1) := by
    rw [show 2 * j + 2 = (2 * j + 1) + 1 by omega, pow_succ]
    calc
      ρ * ((ρ⁻¹) ^ (2 * j + 1) * ρ⁻¹) =
          (ρ⁻¹) ^ (2 * j + 1) * (ρ * ρ⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hρ0, mul_one]
  rw [← hpow]
  ring

/-- The fixed-circle Bessel inequality after multiplying by the polar
Jacobian `2ρ`; its finite left side is integrated in `RadialFinite`. -/
theorem exteriorRadialFiniteEnergy_le_circle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {ρ : ℝ} (hρ : 1 < ρ) (N : ℕ) :
    2 * ρ + ∑ j ∈ Finset.Icc 1 N,
      ‖exteriorForwardCoeff F j‖ ^ 2 *
        (2 * (j : ℝ) ^ 2 * (ρ⁻¹) ^ (2 * j + 1)) ≤
      2 * ρ *
        (∫ θ : AddCircle (2 * Real.pi),
          ‖deriv F (exteriorCirclePoint ρ θ)‖ ^ 2
            ∂(@haarAddCircle (2 * Real.pi) _)) := by
  have hρpos : 0 < ρ := by linarith
  rw [exteriorRadialFiniteEnergy_eq_modes F hρpos N]
  exact mul_le_mul_of_nonneg_left
    (exteriorDerivativeCircle_finite_energy_le F hc hρ N)
    (by positivity : 0 ≤ 2 * ρ)

end SpringerLean
