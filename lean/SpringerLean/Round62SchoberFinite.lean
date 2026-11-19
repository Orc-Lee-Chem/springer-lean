import SpringerLean.Round61FifthMomentBridge
import Mathlib.RingTheory.PowerSeries.Inverse

namespace SpringerLean

open PowerSeries

/-- Reciprocal coordinate of an inverse Laurent series w - B(1/w). -/
noncomputable def schoberReciprocalSeries (B : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.X * (1 - PowerSeries.X * B)⁻¹

/-- Its first three coefficients require only B(0)=0 and B₁. -/
theorem schoberReciprocalSeries_first_three
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    PowerSeries.coeff 1 (schoberReciprocalSeries B) = 1 ∧
    PowerSeries.coeff 2 (schoberReciprocalSeries B) = 0 ∧
    PowerSeries.coeff 3 (schoberReciprocalSeries B) =
      PowerSeries.coeff 1 B := by
  let D : PowerSeries ℂ := 1 - PowerSeries.X * B
  let R : PowerSeries ℂ := D⁻¹
  have hD0 : PowerSeries.coeff 0 D = 1 := by
    simp [D]
  have hD1 : PowerSeries.coeff 1 D = 0 := by
    simp [D, PowerSeries.coeff_succ_X_mul, hB0]
  have hD2 : PowerSeries.coeff 2 D = -PowerSeries.coeff 1 B := by
    simp [D, PowerSeries.coeff_succ_X_mul]
  have hDconst : PowerSeries.constantCoeff D = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hD0
  have hDR : D * R = 1 := by
    exact PowerSeries.mul_inv_cancel D (by simp [hDconst])
  have hR0 : PowerSeries.coeff 0 R = 1 := by
    simp [R, PowerSeries.coeff_zero_eq_constantCoeff, hDconst]
  have hR1 : PowerSeries.coeff 1 R = 0 := by
    have h := congrArg (PowerSeries.coeff 1) hDR
    rw [PowerSeries.coeff_one_mul] at h
    simp [hDconst, hD1, hR0] at h
    exact h
  have hR2 : PowerSeries.coeff 2 R = PowerSeries.coeff 1 B := by
    have h := congrArg (PowerSeries.coeff 2) hDR
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    norm_num [Finset.sum_range_succ, hD0, hD1, hD2, hR0, hR1] at h
    linear_combination h
  change PowerSeries.coeff 1 (PowerSeries.X * R) = 1 ∧
    PowerSeries.coeff 2 (PowerSeries.X * R) = 0 ∧
    PowerSeries.coeff 3 (PowerSeries.X * R) = PowerSeries.coeff 1 B
  simp [PowerSeries.coeff_succ_X_mul, hR0, hR1, hR2]


/-- The order-three functional applied to the formal reciprocal of an inverse Laurent series. -/
noncomputable def schoberFiniteL (B : PowerSeries ℂ) (j : ℕ) : ℂ :=
  PowerSeries.coeff 3 ((schoberReciprocalSeries B) ^ j)

/-- Exact finite L values; terms of order greater than three vanish. -/
theorem schoberFiniteL_values
    (B : PowerSeries ℂ) (hB0 : PowerSeries.coeff 0 B = 0) :
    schoberFiniteL B 1 = PowerSeries.coeff 1 B ∧
      schoberFiniteL B 2 = 0 ∧
      schoberFiniteL B 3 = 1 ∧
      (∀ j : ℕ, 3 < j → schoberFiniteL B j = 0) := by
  let D : PowerSeries ℂ := 1 - PowerSeries.X * B
  let R : PowerSeries ℂ := D⁻¹
  have hS := schoberReciprocalSeries_first_three B hB0
  have hR0 : PowerSeries.coeff 0 R = 1 := by
    simp [R, D, PowerSeries.coeff_zero_eq_constantCoeff]
  have hR1 : PowerSeries.coeff 1 R = 0 := by
    have h := hS.2.1
    change PowerSeries.coeff 2 (PowerSeries.X * R) = 0 at h
    simpa only [PowerSeries.coeff_succ_X_mul] using h
  constructor
  · simpa [schoberFiniteL] using hS.2.2
  constructor
  · change PowerSeries.coeff 3 ((PowerSeries.X * R) ^ 2) = 0
    rw [mul_pow]
    have hs := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 1
    have hp : PowerSeries.coeff 1 (R ^ 2) = 0 := by
      rw [PowerSeries.coeff_one_pow]
      simp [hR1]
    simpa [pow_mul] using hs.trans hp
  constructor
  · change PowerSeries.coeff 3 ((PowerSeries.X * R) ^ 3) = 1
    rw [mul_pow]
    have hs := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 0
    have hRconst : PowerSeries.constantCoeff R = 1 := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hR0
    have hp : PowerSeries.coeff 0 (R ^ 3) = 1 := by
      simp [PowerSeries.coeff_zero_eq_constantCoeff, hRconst]
    simpa [pow_mul] using hs.trans hp
  · intro j hj
    change PowerSeries.coeff 3 ((PowerSeries.X * R) ^ j) = 0
    rw [mul_pow]
    have hz := PowerSeries.coeff_X_pow_mul' (R ^ j) j 3
    simp [Nat.not_le.mpr hj, pow_mul] at hz ⊢
    exact hz

/-- Actual inverse coefficients, independently read by differentiation, form this series. -/
noncomputable def schoberActualInverseSeries (F : ℂ → ℂ) : PowerSeries ℂ :=
  actualTaylorSeries (exteriorInverseGerm F)

theorem schoberActualInverseSeries_coeff_zero (F : ℂ → ℂ) :
    PowerSeries.coeff 0 (schoberActualInverseSeries F) = 0 := by
  simp [schoberActualInverseSeries, actualTaylorCoeff, exteriorInverseGerm]

theorem schoberActualInverseSeries_coeff_one (F : ℂ → ℂ) :
    PowerSeries.coeff 1 (schoberActualInverseSeries F) =
      exteriorInverseCoeff F 1 := by
  simpa [schoberActualInverseSeries] using (actualTaylorCoeff_inverse F 1)

/-- L-values obtained from the actual inverse's Laurent coefficients (formal reciprocal). -/
theorem schoberActualFiniteL_values
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFiniteL (schoberActualInverseSeries F) 1 =
        exteriorForwardCoeff F 1 ∧
      schoberFiniteL (schoberActualInverseSeries F) 2 = 0 ∧
      schoberFiniteL (schoberActualInverseSeries F) 3 = 1 ∧
      (∀ j : ℕ, 3 < j →
        schoberFiniteL (schoberActualInverseSeries F) j = 0) := by
  simpa [schoberActualInverseSeries_coeff_one,
    exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] using
    schoberFiniteL_values (schoberActualInverseSeries F)
      (schoberActualInverseSeries_coeff_zero F)


/-- The d=1 squared test-vector norm, with the Grunsky weights 1/i. -/
theorem schoberActualFiniteL_energy_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (∑ i ∈ Finset.Icc 1 3,
      ‖schoberFiniteL (schoberActualInverseSeries F) i‖ ^ 2 / (i : ℝ)) =
        ‖exteriorForwardCoeff F 1‖ ^ 2 + 1 / 3 := by
  let L := schoberFiniteL (schoberActualInverseSeries F)
  have hL := schoberActualFiniteL_values F hc
  have h1 : L 1 = exteriorForwardCoeff F 1 := hL.1
  have h2 : L 2 = 0 := hL.2.1
  have h3 : L 3 = 1 := hL.2.2.1
  norm_num [Finset.sum_Icc_succ_top, L, h1, h2, h3]

/-- The d=2 test vector has only (1,2) and (2,1), total squared norm one. -/
theorem schoberActualFiniteL_energy_two
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (∑ i ∈ Finset.Icc 1 3,
      ∑ j ∈ Finset.Icc 1 3,
        ‖schoberFiniteL (schoberActualInverseSeries F) (i + j)‖ ^ 2 /
          ((i : ℝ) * (j : ℝ))) = 1 := by
  let L := schoberFiniteL (schoberActualInverseSeries F)
  have hL := schoberActualFiniteL_values F hc
  have h2 : L 2 = 0 := hL.2.1
  have h3 : L 3 = 1 := hL.2.2.1
  have h4 : L 4 = 0 := hL.2.2.2 4 (by omega)
  have h5 : L 5 = 0 := hL.2.2.2 5 (by omega)
  have h6 : L 6 = 0 := hL.2.2.2 6 (by omega)
  norm_num [Finset.sum_Icc_succ_top, L, h2, h3, h4, h5, h6]

/-- The d=3 test vector has only (1,1,1), total squared norm one. -/
theorem schoberActualFiniteL_energy_three
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (∑ i ∈ Finset.Icc 1 3,
      ∑ j ∈ Finset.Icc 1 3,
        ∑ k ∈ Finset.Icc 1 3,
          ‖schoberFiniteL (schoberActualInverseSeries F) (i + j + k)‖ ^ 2 /
            ((i : ℝ) * (j : ℝ) * (k : ℝ))) = 1 := by
  let L := schoberFiniteL (schoberActualInverseSeries F)
  have hL := schoberActualFiniteL_values F hc
  have h3 : L 3 = 1 := hL.2.2.1
  have h4 : L 4 = 0 := hL.2.2.2 4 (by omega)
  have h5 : L 5 = 0 := hL.2.2.2 5 (by omega)
  have h6 : L 6 = 0 := hL.2.2.2 6 (by omega)
  have h7 : L 7 = 0 := hL.2.2.2 7 (by omega)
  have h8 : L 8 = 0 := hL.2.2.2 8 (by omega)
  have h9 : L 9 = 0 := hL.2.2.2 9 (by omega)
  norm_num [Finset.sum_Icc_succ_top, L, h3, h4, h5, h6, h7, h8, h9]

end SpringerLean