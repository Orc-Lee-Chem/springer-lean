import SpringerLean.Round1727ActualDriftFluxPowerBound

namespace SpringerLean

/-- The phase-gradient P flux has |H|^(2k-1) size whenever the two
gradient coordinates have their local |H|^(k-1) bounds. -/
theorem actualEnergyFluxPField_norm_le_power
    (F : ℂ → ℂ) (k : ℕ) (hk : 1 ≤ k)
    (beta z : ℂ) (hbeta : ‖beta‖ = 1)
    (Cchi Cg : ℝ) (hCchi : 0 ≤ Cchi) (hCg : 0 ≤ Cg)
    (hchi : |energyMultiplierChi (actualHarmonicMultiplierTime F k z)| ≤ Cchi)
    (hx : |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ)| ≤
      Cg * ‖actualHarmonic F z‖^(k - 1))
    (hy : |(fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I| ≤
      Cg * ‖actualHarmonic F z‖^(k - 1)) :
    ‖actualEnergyFluxPField F k beta z‖ ≤
      2 * Cchi * Cg * ‖actualHarmonic F z‖^(2 * k - 1) := by
  let y := ‖actualHarmonic F z‖
  let U := actualHarmonicPhaseField F k beta z
  let chi := energyMultiplierChi (actualHarmonicMultiplierTime F k z)
  let ux := (fderiv ℝ (actualHarmonicPhaseField F k beta) z) (1 : ℂ)
  let uy := (fderiv ℝ (actualHarmonicPhaseField F k beta) z) Complex.I
  have hU := actualHarmonicPhaseField_abs_le_power F k beta z hbeta
  have hpow : y^k * y^(k - 1) = y^(2 * k - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have htermx : |chi * U * ux| ≤ Cchi * Cg * y^(2 * k - 1) := by
    rw [abs_mul, abs_mul]
    calc
      |chi| * |U| * |ux| ≤ Cchi * y^k * (Cg * y^(k - 1)) := by
        gcongr
      _ = Cchi * Cg * y^(2 * k - 1) := by rw [← hpow]; ring
  have htermy : |chi * U * uy| ≤ Cchi * Cg * y^(2 * k - 1) := by
    rw [abs_mul, abs_mul]
    calc
      |chi| * |U| * |uy| ≤ Cchi * y^k * (Cg * y^(k - 1)) := by
        gcongr
      _ = Cchi * Cg * y^(2 * k - 1) := by rw [← hpow]; ring
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (actualEnergyFluxPField F k beta z)
  change ‖actualEnergyFluxPField F k beta z‖ ≤
    |chi * U * ux| + |chi * U * uy| at hnorm
  nlinarith [hnorm, htermx, htermy]

end SpringerLean

#print axioms SpringerLean.actualEnergyFluxPField_norm_le_power
