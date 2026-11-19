import SpringerLean.Round1728ActualPFluxPowerBound

namespace SpringerLean

/-- A common |H|^(2k-1) bound for the signed actual combined flux,
with only pointwise multiplier and phase-gradient hypotheses. -/
theorem actualEnergyFluxField_norm_le_power
    (F : ℂ → ℂ) (k : ℕ) (hk : 2 ≤ k)
    (beta z : ℂ) (hbeta : ‖beta‖ = 1)
    (hH : actualHarmonic F z ≠ 0)
    (Cchi Cf Cs Cg : ℝ)
    (hchi : |energyMultiplierChi (actualHarmonicMultiplierTime F k z)| ≤ Cchi)
    (hf : |energyMultiplierF (actualHarmonicMultiplierTime F k z)| ≤ Cf)
    (hs : |energyMultiplierSigma (actualHarmonicMultiplierTime F k z)| ≤ Cs)
    (hx : |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ)| ≤
      Cg * ‖actualHarmonic F z‖^(k - 1))
    (hy : |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I| ≤
      Cg * ‖actualHarmonic F z‖^(k - 1)) :
    ‖actualEnergyFluxField F k beta z‖ ≤
      (2 * Cchi * Cg + 8 * ((k : ℝ) - 1) * Cf +
        4 * ((k : ℝ) - 1) * Cs) *
        ‖actualHarmonic F z‖^(2 * k - 1) := by
  let y := ‖actualHarmonic F z‖
  let P := actualEnergyFluxPField F k beta z
  let R := actualEnergyFluxRField F k beta z
  let S := actualEnergyFluxSField F k beta z
  let a : ℝ := 4 * ((k : ℝ) - 1)
  let b : ℝ := 2 * ((k : ℝ) - 1)
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hCchi : 0 ≤ Cchi := (abs_nonneg _).trans hchi
  have hCf : 0 ≤ Cf := (abs_nonneg _).trans hf
  have hCs : 0 ≤ Cs := (abs_nonneg _).trans hs
  have hCg : 0 ≤ Cg := by
    have hpow : 0 < y^(k - 1) := pow_pos (norm_pos_iff.mpr hH) _
    have h := (abs_nonneg _).trans hx
    nlinarith
  have hP : ‖P‖ ≤ 2 * Cchi * Cg * y^(2 * k - 1) :=
    actualEnergyFluxPField_norm_le_power F k (by omega) beta z
      hbeta Cchi Cg hCchi hCg hchi hx hy
  have hR : ‖R‖ ≤ 2 * Cf * y^(2 * k - 1) :=
    actualEnergyFluxRField_norm_le_power F k (by omega)
      beta z hbeta hH Cf hf
  have hS : ‖S‖ ≤ 2 * Cs * y^(2 * k - 1) :=
    actualEnergyFluxSField_norm_le_power F k (by omega)
      beta z hbeta hH Cs hs
  have hRm := mul_le_mul_of_nonneg_left hR ha
  have hSm := mul_le_mul_of_nonneg_left hS hb
  have htri : ‖actualEnergyFluxField F k beta z‖ ≤
      ‖P‖ + a * ‖R‖ + b * ‖S‖ := by
    change ‖P + a • R - b • S‖ ≤ _
    calc
      ‖P + a • R - b • S‖ ≤ ‖P + a • R‖ + ‖b • S‖ :=
        norm_sub_le _ _
      _ ≤ (‖P‖ + ‖a • R‖) + ‖b • S‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖P‖ + a * ‖R‖ + b * ‖S‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
  dsimp only [a, b, y] at hRm hSm htri hP ⊢
  nlinarith [hP, hRm, hSm, htri]

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxField_norm_le_power
