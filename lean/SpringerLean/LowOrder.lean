import SpringerLean.AnalyticReversion

namespace SpringerLean

open PowerSeries

theorem exteriorFormalForward_coeff_zero (F : ℂ → ℂ) :
    PowerSeries.coeff 0 (exteriorFormalForward F) = 0 := by
  simp [exteriorFormalForward_coeff, exteriorForwardCoeff, exteriorForwardGerm]

theorem exteriorFormalResidue_two (F : ℂ → ℂ) :
    exteriorFormalResidue F 2 = 2 * exteriorForwardCoeff F 2 := by
  let f := exteriorFormalForward F
  have hf0 : PowerSeries.coeff 0 f = 0 :=
    exteriorFormalForward_coeff_zero F
  change PowerSeries.coeff 3 ((formalExteriorPhi f) ^ 2) =
    2 * exteriorForwardCoeff F 2
  rw [← exteriorFormalForward_coeff F 2]
  change PowerSeries.coeff 3 ((1 + PowerSeries.X * f) ^ 2) =
    2 * PowerSeries.coeff 2 f
  have hpow : (1 + PowerSeries.X * f) ^ 2 =
      1 + 2 * (PowerSeries.X * f) + PowerSeries.X ^ 2 * f ^ 2 := by ring
  rw [hpow]
  have hshift :
      PowerSeries.coeff 3 (PowerSeries.X ^ 2 * f ^ 2) =
      PowerSeries.coeff 1 (f ^ 2) := by
    simpa using PowerSeries.coeff_X_pow_mul (f ^ 2) 2 1
  rw [map_add, map_add, hshift]
  have hconst : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf0
  simp [PowerSeries.coeff_succ_X_mul, pow_two,
    PowerSeries.coeff_one_mul, hconst]

theorem exteriorInverseCoeff_two_eq_forwardCoeff_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 2 = exteriorForwardCoeff F 2 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 2 (by omega)
  rw [exteriorFormalResidue_two] at h
  exact (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h)

theorem exteriorFormalResidue_three (F : ℂ → ℂ) :
    exteriorFormalResidue F 3 =
      3 * (exteriorForwardCoeff F 3 +
        (exteriorForwardCoeff F 1) ^ 2) := by
  let f := exteriorFormalForward F
  have hf0 : PowerSeries.coeff 0 f = 0 :=
    exteriorFormalForward_coeff_zero F
  have hconst : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hf0
  change PowerSeries.coeff 4 ((formalExteriorPhi f) ^ 3) =
    3 * (exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2)
  rw [← exteriorFormalForward_coeff F 3,
    ← exteriorFormalForward_coeff F 1]
  change PowerSeries.coeff 4 ((1 + PowerSeries.X * f) ^ 3) =
    3 * (PowerSeries.coeff 3 f + (PowerSeries.coeff 1 f) ^ 2)
  have hpow : (1 + PowerSeries.X * f) ^ 3 =
      1 + 3 * (PowerSeries.X * f) +
        3 * (PowerSeries.X ^ 2 * f ^ 2) +
        PowerSeries.X ^ 3 * f ^ 3 := by ring
  rw [hpow]
  have hs2 : PowerSeries.coeff 4 (PowerSeries.X ^ 2 * f ^ 2) =
      PowerSeries.coeff 2 (f ^ 2) := by
    simpa using PowerSeries.coeff_X_pow_mul (f ^ 2) 2 2
  have hs3 : PowerSeries.coeff 4 (PowerSeries.X ^ 3 * f ^ 3) =
      PowerSeries.coeff 1 (f ^ 3) := by
    simpa using PowerSeries.coeff_X_pow_mul (f ^ 3) 3 1
  rw [map_add, map_add, map_add]
  simp only [PowerSeries.coeff_ofNat_mul]
  rw [hs2, hs3]
  have hf2 : PowerSeries.coeff 2 (f ^ 2) = (PowerSeries.coeff 1 f) ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ, hf0]
    ring
  have hf3 : PowerSeries.coeff 1 (f ^ 3) = 0 := by
    rw [pow_succ, PowerSeries.coeff_one_mul]
    simp [hconst]
  simp [PowerSeries.coeff_succ_X_mul, hf2, hf3]
  ring

theorem exteriorInverseCoeff_three_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 3 =
      exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 3 (by omega)
  rw [exteriorFormalResidue_three] at h
  exact (mul_left_cancel₀ (by norm_num : (3 : ℂ) ≠ 0) h)
theorem exteriorInverseCoeff_slitMap_three (a : ℂ) (ha : ‖a‖ = 1) :
    exteriorInverseCoeff (slitMap a) 3 = a ^ 2 := by
  rw [exteriorInverseCoeff_slitMap]
  exact (slitTaylorCoeff_first_two a ha).2

end SpringerLean