import SpringerLean.Round102ThirdMode

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The seventh inverse coefficient's formal residue, with the manuscript's
actual forward coefficients and the project's minus-sign inverse convention. -/
theorem exteriorFormalResidue_seven (F : ℂ → ℂ) :
    exteriorFormalResidue F 7 =
      7 * (exteriorForwardCoeff F 7 +
        6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
        6 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 3 ^ 2 +
        15 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 3 +
        15 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 2 +
        5 * exteriorForwardCoeff F 1 ^ 4) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let A : PowerSeries ℂ := PowerSeries.X ^ 2 * g
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : formalExteriorPhi f = 1 + A := by
    rw [formalExteriorPhi, hf]
    dsimp [A]
    ring
  have hg (p : ℕ) : PowerSeries.coeff p g = exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hg0 : PowerSeries.constantCoeff g = exteriorForwardCoeff F 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hs1 : PowerSeries.coeff 8 A = exteriorForwardCoeff F 7 := by
    dsimp [A]
    rw [show 8 = 6 + 2 by omega, PowerSeries.coeff_X_pow_mul, hg]
  have hs2 : PowerSeries.coeff 8 (A ^ 2) = PowerSeries.coeff 4 (g ^ 2) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 2) 4 4 using 1 <;> ring
  have hs3 : PowerSeries.coeff 8 (A ^ 3) = PowerSeries.coeff 2 (g ^ 3) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 3) 6 2 using 1 <;> ring
  have hs4 : PowerSeries.coeff 8 (A ^ 4) = PowerSeries.coeff 0 (g ^ 4) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 4) 8 0 using 1 <;> ring
  have hs5 : PowerSeries.coeff 8 (A ^ 5) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 5) 10 8 using 1 <;> ring_nf <;> norm_num
  have hs6 : PowerSeries.coeff 8 (A ^ 6) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 6) 12 8 using 1 <;> ring_nf <;> norm_num
  have hs7 : PowerSeries.coeff 8 (A ^ 7) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 7) 14 8 using 1 <;> ring_nf <;> norm_num
  have hsq4 : PowerSeries.coeff 4 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      exteriorForwardCoeff F 3 ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hg0, hg]
    ring
  have hsq0 : PowerSeries.coeff 0 (g ^ 2) = (exteriorForwardCoeff F 1) ^ 2 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hg0]
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
    rw [PowerSeries.coeff_one_pow]
    simp [hg0, hg]
    ring
  have hsq2 : PowerSeries.coeff 2 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      exteriorForwardCoeff F 2 ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hg0, hg]
    ring
  have hcube2 : PowerSeries.coeff 2 (g ^ 3) =
      3 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 3 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 2 := by
    rw [show g ^ 3 = g ^ 2 * g by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hsq0, hsq1, hsq2, hg]
    simp [hg0]
    ring
  have hfour0 : PowerSeries.coeff 0 (g ^ 4) =
      exteriorForwardCoeff F 1 ^ 4 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hg0]
  have hpow : (1 + A) ^ 7 =
      1 + 7 * A + 21 * A ^ 2 + 35 * A ^ 3 +
        35 * A ^ 4 + 21 * A ^ 5 + 7 * A ^ 6 + A ^ 7 := by ring
  change PowerSeries.coeff 8 ((formalExteriorPhi f) ^ 7) = _
  rw [hphi, hpow]
  simp only [map_add, PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_ofNat_mul, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  rw [hsq4, hcube2, hfour0]
  simp
  ring

theorem exteriorInverseCoeff_seven_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 7 =
      exteriorForwardCoeff F 7 +
        6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
        6 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 3 ^ 2 +
        15 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 3 +
        15 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 ^ 2 +
        5 * exteriorForwardCoeff F 1 ^ 4 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 7 (by omega)
  rw [exteriorFormalResidue_seven] at h
  exact mul_left_cancel₀ (by norm_num : (7 : ℂ) ≠ 0) h

end SpringerLean
