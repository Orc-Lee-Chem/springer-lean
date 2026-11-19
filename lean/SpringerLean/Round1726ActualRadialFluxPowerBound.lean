import SpringerLean.Round1725PhasePowerDivision

namespace SpringerLean

/-- A coarse Cartesian estimate is sufficient for the zero extension:
the actual radial flux has at most |H|^(2k-1) size. The harmless factor
two avoids any norm calculation for a complex quotient. -/
theorem actualEnergyFluxRField_norm_le_power
    (F : ℂ → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (beta z : ℂ) (hbeta : ‖beta‖ = 1)
    (hH : actualHarmonic F z ≠ 0) (Cf : ℝ)
    (hf : |energyMultiplierF (actualHarmonicMultiplierTime F k z)| ≤ Cf) :
    ‖actualEnergyFluxRField F k beta z‖ ≤
      2 * Cf * ‖actualHarmonic F z‖^(2 * k - 1) := by
  let y := ‖actualHarmonic F z‖
  let U := actualHarmonicPhaseField F k beta z
  let phi := energyMultiplierF (actualHarmonicMultiplierTime F k z)
  let a := phi * U^2 / y
  have hy : 0 < y := norm_pos_iff.mpr hH
  have hU := actualHarmonicPhaseField_abs_le_power F k beta z hbeta
  have hquot : U^2 / y ≤ y^(2 * k - 1) :=
    phase_square_div_le_power y U k hk hy hU
  have hquot0 : 0 ≤ U^2 / y := by positivity
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans hf
  have hscalar : |a| ≤ Cf * y^(2 * k - 1) := by
    have ha : a = phi * (U^2 / y) := by dsimp [a]; ring
    rw [ha, abs_mul, abs_of_nonneg hquot0]
    exact (mul_le_mul_of_nonneg_right hf hquot0).trans
      (mul_le_mul_of_nonneg_left hquot hCf)
  by_cases hz : z = 0
  · have hJ : actualEnergyFluxRField F k beta z = 0 := by
      apply Complex.ext <;> simp [actualEnergyFluxRField, hz]
    rw [hJ, norm_zero]
    positivity
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    have hxa : |a * z.re / ‖z‖| ≤ |a| := by
      rw [abs_div, abs_mul, abs_norm]
      exact (div_le_iff₀ hr).mpr
        (mul_le_mul_of_nonneg_left hre (abs_nonneg a))
    have hya : |a * z.im / ‖z‖| ≤ |a| := by
      rw [abs_div, abs_mul, abs_norm]
      exact (div_le_iff₀ hr).mpr
        (mul_le_mul_of_nonneg_left him (abs_nonneg a))
    have hcart : ‖actualEnergyFluxRField F k beta z‖ ≤ 2 * |a| := by
      have hnorm := Complex.norm_le_abs_re_add_abs_im
        (actualEnergyFluxRField F k beta z)
      change ‖actualEnergyFluxRField F k beta z‖ ≤
        |a * z.re / ‖z‖| + |a * z.im / ‖z‖| at hnorm
      nlinarith [hnorm, hxa, hya]
    have hh := mul_le_mul_of_nonneg_left hscalar (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [a, y, U, phi] at hcart hh ⊢
    exact hcart.trans (by nlinarith [hh])

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxRField_norm_le_power
