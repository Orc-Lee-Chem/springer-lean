import SpringerLean.Round141SixthArithmetic

namespace SpringerLean
open PowerSeries

theorem exteriorFormalResidue_six (F : ℂ → ℂ) :
    exteriorFormalResidue F 6 = 6 *
      (exteriorForwardCoeff F 6 +
        5 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
        5 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 +
        10 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2) := by
  let g := schoberActualForwardShift F
  let A : PowerSeries ℂ := PowerSeries.X ^ 2 * g
  have hf0 : PowerSeries.constantCoeff (exteriorFormalForward F) = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : exteriorFormalForward F = PowerSeries.X * g := by
    simpa [g, schoberActualForwardShift, hf0] using
      PowerSeries.eq_X_mul_shift_add_const (exteriorFormalForward F)
  have hφ : formalExteriorPhi (exteriorFormalForward F) = 1 + A := by
    rw [formalExteriorPhi, hf]
    dsimp [A]
    ring
  have hg (p : ℕ) : PowerSeries.coeff p g = exteriorForwardCoeff F (p + 1) :=
    schoberActualForwardShift_coeff F p
  have hgc : PowerSeries.constantCoeff g = exteriorForwardCoeff F 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hs1 : PowerSeries.coeff 7 A = exteriorForwardCoeff F 6 := by
    simpa [A, hg] using PowerSeries.coeff_X_pow_mul g 2 5
  have hs2 : PowerSeries.coeff 7 (A ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 := by
    dsimp [A]
    rw [mul_pow, ← pow_mul]
    norm_num only [Nat.reduceMul]
    rw [show 7 = 3 + 4 by omega, PowerSeries.coeff_X_pow_mul]
    rw [show g ^ 2 = g * g by ring, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, hg]
    ring
  have hs3 : PowerSeries.coeff 7 (A ^ 3) =
      3 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 := by
    dsimp [A]
    rw [mul_pow, ← pow_mul]
    norm_num only [Nat.reduceMul]
    rw [show 7 = 1 + 6 by omega, PowerSeries.coeff_X_pow_mul]
    rw [show g ^ 3 = (g * g) * g by ring]
    simp only [PowerSeries.coeff_one_mul, PowerSeries.coeff_zero_eq_constantCoeff,
      map_mul, hgc, hg]
    ring
  have hs (d : ℕ) (hd : 4 ≤ d) : PowerSeries.coeff 7 (A ^ d) = 0 := by
    dsimp [A]
    rw [mul_pow, ← pow_mul, PowerSeries.coeff_X_pow_mul']
    simp [show ¬ 2 * d ≤ 7 by omega]
  have hpow : (1 + A) ^ 6 =
      1 + 6 * A + 15 * A ^ 2 + 20 * A ^ 3 +
        15 * A ^ 4 + 6 * A ^ 5 + A ^ 6 := by ring
  change PowerSeries.coeff 7 (formalExteriorPhi (exteriorFormalForward F) ^ 6) = _
  rw [hφ, hpow]
  simp only [map_add, PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_ofNat_mul, hs1, hs2, hs3, hs 4 (by omega),
    hs 5 (by omega), hs 6 (by omega)]
  simp
  ring

theorem exteriorInverseCoeff_six_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 6 = exteriorForwardCoeff F 6 +
      5 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      5 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 +
      10 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 6 (by omega)
  rw [exteriorFormalResidue_six F] at h
  exact mul_left_cancel₀ (by norm_num : (6 : ℂ) ≠ 0) h

end SpringerLean
