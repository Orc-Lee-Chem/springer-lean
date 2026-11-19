import SpringerLean.Round1726ActualRadialFluxPowerBound

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual drift flux has the same |H|^(2k-1) vanishing order.
The factor two comes from the two Cartesian coordinate estimates. -/
theorem actualEnergyFluxSField_norm_le_power
    (F : ℂ → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (beta z : ℂ) (hbeta : ‖beta‖ = 1)
    (hH : actualHarmonic F z ≠ 0) (Cs : ℝ)
    (hs : |energyMultiplierSigma (actualHarmonicMultiplierTime F k z)| ≤ Cs) :
    ‖actualEnergyFluxSField F k beta z‖ ≤
      2 * Cs * ‖actualHarmonic F z‖^(2 * k - 1) := by
  let y := ‖actualHarmonic F z‖
  let U := actualHarmonicPhaseField F k beta z
  let sigma := energyMultiplierSigma (actualHarmonicMultiplierTime F k z)
  let Q := (conj (actualHarmonic F z))⁻¹
  let a := sigma * U^2
  have hy : 0 < y := norm_pos_iff.mpr hH
  have hU := actualHarmonicPhaseField_abs_le_power F k beta z hbeta
  have hquot : U^2 / y ≤ y^(2 * k - 1) :=
    phase_square_div_le_power y U k hk hy hU
  have hquot0 : 0 ≤ U^2 / y := by positivity
  have hCs : 0 ≤ Cs := (abs_nonneg _).trans hs
  have hQ : ‖Q‖ = 1 / y := by
    simp [Q, y, norm_inv, Complex.norm_conj, one_div]
  have hscalar : |a| * ‖Q‖ ≤ Cs * y^(2 * k - 1) := by
    rw [hQ]
    have ha : |a| = |sigma| * U^2 := by
      simp [a, abs_mul, abs_of_nonneg (sq_nonneg U)]
    rw [ha]
    have hmul : |sigma| * U^2 * (1 / y) =
        |sigma| * (U^2 / y) := by ring
    rw [hmul]
    exact (mul_le_mul_of_nonneg_right hs hquot0).trans
      (mul_le_mul_of_nonneg_left hquot hCs)
  have hre : |Q.re| ≤ ‖Q‖ := Complex.abs_re_le_norm Q
  have him : |Q.im| ≤ ‖Q‖ := Complex.abs_im_le_norm Q
  have hxa : |a * Q.re| ≤ |a| * ‖Q‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hre (abs_nonneg a)
  have hya : |a * Q.im| ≤ |a| * ‖Q‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left him (abs_nonneg a)
  have hcart : ‖actualEnergyFluxSField F k beta z‖ ≤ 2 * (|a| * ‖Q‖) := by
    have hnorm := Complex.norm_le_abs_re_add_abs_im
      (actualEnergyFluxSField F k beta z)
    change ‖actualEnergyFluxSField F k beta z‖ ≤
      |a * Q.re| + |a * Q.im| at hnorm
    nlinarith [hnorm, hxa, hya]
  have hh := mul_le_mul_of_nonneg_left hscalar (by norm_num : (0 : ℝ) ≤ 2)
  dsimp only [a, Q, y, U, sigma] at hcart hh ⊢
  exact hcart.trans (by nlinarith [hh])

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxSField_norm_le_power
