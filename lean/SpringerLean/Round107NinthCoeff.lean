import SpringerLean.Round106FifthDiagonal

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- The actual ninth inverse coefficient, obtained from the formal residue
of the same forward map and the verified analytic inverse bridge. -/
theorem exteriorFormalResidue_nine (F : ℂ → ℂ) :
    exteriorFormalResidue F 9 =
      9 * (exteriorForwardCoeff F 9 +
        8 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
        8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
        8 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
        4 * exteriorForwardCoeff F 4 ^ 2 +
        28 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 5 +
        56 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 4 +
        28 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 ^ 2 +
        28 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 3 +
        56 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 3 +
        84 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 ^ 2 +
        14 * exteriorForwardCoeff F 1 ^ 5) := by
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
  have hs1 : PowerSeries.coeff 10 A = exteriorForwardCoeff F 9 := by
    dsimp [A]
    rw [show 10 = 8 + 2 by omega, PowerSeries.coeff_X_pow_mul, hg]
  have hs2 : PowerSeries.coeff 10 (A ^ 2) = PowerSeries.coeff 6 (g ^ 2) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 2) 4 6 using 1 <;> ring
  have hs3 : PowerSeries.coeff 10 (A ^ 3) = PowerSeries.coeff 4 (g ^ 3) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 3) 6 4 using 1 <;> ring
  have hs4 : PowerSeries.coeff 10 (A ^ 4) = PowerSeries.coeff 2 (g ^ 4) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 4) 8 2 using 1 <;> ring
  have hs5 : PowerSeries.coeff 10 (A ^ 5) = PowerSeries.coeff 0 (g ^ 5) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 5) 10 0 using 1 <;> ring
  have hs6 : PowerSeries.coeff 10 (A ^ 6) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 6) 12 10 using 1 <;> ring_nf <;> norm_num
  have hs7 : PowerSeries.coeff 10 (A ^ 7) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 7) 14 10 using 1 <;> ring_nf <;> norm_num
  have hs8 : PowerSeries.coeff 10 (A ^ 8) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 8) 16 10 using 1 <;> ring_nf <;> norm_num
  have hs9 : PowerSeries.coeff 10 (A ^ 9) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 9) 18 10 using 1 <;> ring_nf <;> norm_num
  have hsq0 : PowerSeries.coeff 0 (g ^ 2) = exteriorForwardCoeff F 1 ^ 2 := by
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
  have hsq3 : PowerSeries.coeff 3 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hg0, hg]
    ring
  have hsq4 : PowerSeries.coeff 4 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      exteriorForwardCoeff F 3 ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hg0, hg]
    ring
  have hsq6 : PowerSeries.coeff 6 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
      2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
      2 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
      exteriorForwardCoeff F 4 ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hg0, hg]
    ring
  have hcube4 : PowerSeries.coeff 4 (g ^ 3) =
      3 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 5 +
      6 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 4 +
      3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 ^ 2 +
      3 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 3 := by
    rw [show g ^ 3 = g ^ 2 * g by ring,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hsq0, hsq1, hsq2, hsq3, hsq4, hg]
    simp [hg0]
    ring
  have hfour2 : PowerSeries.coeff 2 (g ^ 4) =
      4 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 3 +
      6 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 ^ 2 := by
    rw [show g ^ 4 = (g ^ 2) ^ 2 by ring, pow_two,
      PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hsq0, hsq1, hsq2]
    simp [hg0]
    ring
  have hfive0 : PowerSeries.coeff 0 (g ^ 5) = exteriorForwardCoeff F 1 ^ 5 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hg0]
  have hpow : (1 + A) ^ 9 =
      1 + 9 * A + 36 * A ^ 2 + 84 * A ^ 3 +
      126 * A ^ 4 + 126 * A ^ 5 + 84 * A ^ 6 +
      36 * A ^ 7 + 9 * A ^ 8 + A ^ 9 := by ring
  change PowerSeries.coeff 10 ((formalExteriorPhi f) ^ 9) = _
  rw [hphi, hpow]
  simp only [map_add, PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_ofNat_mul, hs1, hs2, hs3, hs4, hs5,
    hs6, hs7, hs8, hs9]
  rw [hsq6, hcube4, hfour2, hfive0]
  simp
  ring

theorem exteriorInverseCoeff_nine_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 9 =
      exteriorForwardCoeff F 9 +
        8 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
        8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
        8 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
        4 * exteriorForwardCoeff F 4 ^ 2 +
        28 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 5 +
        56 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
          exteriorForwardCoeff F 4 +
        28 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 ^ 2 +
        28 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 3 +
        56 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 3 +
        84 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 ^ 2 +
        14 * exteriorForwardCoeff F 1 ^ 5 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 9 (by omega)
  rw [exteriorFormalResidue_nine] at h
  exact mul_left_cancel₀ (by norm_num : (9 : ℂ) ≠ 0) h

end SpringerLean
