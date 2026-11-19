import SpringerLean.Round64SchoberAlgebra

namespace SpringerLean

open PowerSeries

/-- Coefficients of the normalized difference quotient in the outer variable.
Only inner powers at most three can contribute to the (3,3) coefficient. -/
noncomputable def schoberKernelT1 (b1 b2 b3 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C b1 * PowerSeries.X + PowerSeries.C b2 * PowerSeries.X ^ 2 +
    PowerSeries.C b3 * PowerSeries.X ^ 3
noncomputable def schoberKernelT2 (b2 b3 b4 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C b2 * PowerSeries.X + PowerSeries.C b3 * PowerSeries.X ^ 2 +
    PowerSeries.C b4 * PowerSeries.X ^ 3
noncomputable def schoberKernelT3 (b3 b4 b5 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C b3 * PowerSeries.X + PowerSeries.C b4 * PowerSeries.X ^ 2 +
    PowerSeries.C b5 * PowerSeries.X ^ 3

noncomputable def schoberKernelT (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.X * PowerSeries.C (schoberKernelT1 b1 b2 b3) +
  PowerSeries.X ^ 2 * PowerSeries.C (schoberKernelT2 b2 b3 b4) +
  PowerSeries.X ^ 3 * PowerSeries.C (schoberKernelT3 b3 b4 b5)

noncomputable def schoberBiCoeff (i j : ℕ)
    (p : PowerSeries (PowerSeries ℂ)) : ℂ :=
  PowerSeries.coeff i (PowerSeries.coeff j p)

private theorem schoberKernelT_outer_zero (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 0 (schoberKernelT b1 b2 b3 b4 b5) = 0 := by
  simp [schoberKernelT]

private theorem schoberKernelT_outer_one (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 1 (schoberKernelT b1 b2 b3 b4 b5) =
      schoberKernelT1 b1 b2 b3 := by
  simp [schoberKernelT, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]

private theorem schoberKernelT_outer_two (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 2 (schoberKernelT b1 b2 b3 b4 b5) =
      schoberKernelT2 b2 b3 b4 := by
  simp [schoberKernelT, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]

private theorem schoberKernelT_outer_three (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 3 (schoberKernelT b1 b2 b3 b4 b5) =
      schoberKernelT3 b3 b4 b5 := by
  simp [schoberKernelT, PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]


/-- Third-order truncated formal logarithm of the finite kernel inverse. -/
noncomputable def schoberKernelQ3 (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  let T := schoberKernelT b1 b2 b3 b4 b5
  T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
    PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3

private theorem schoberKernelQ3_outer_one (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 1 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      schoberKernelT1 b1 b2 b3 := by
  let T := schoberKernelT b1 b2 b3 b4 b5
  have h0 := schoberKernelT_outer_zero b1 b2 b3 b4 b5
  have h1 := schoberKernelT_outer_one b1 b2 b3 b4 b5
  have hconst : PowerSeries.constantCoeff T = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h0
  change PowerSeries.coeff 1
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3) = _
  simp [PowerSeries.coeff_one_pow, hconst, h1, T]

private noncomputable def schoberKernelR (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries (PowerSeries ℂ) :=
  PowerSeries.C (schoberKernelT1 b1 b2 b3) +
  PowerSeries.X * PowerSeries.C (schoberKernelT2 b2 b3 b4) +
  PowerSeries.X ^ 2 * PowerSeries.C (schoberKernelT3 b3 b4 b5)

private theorem schoberKernelT_eq_X_mul_R (b1 b2 b3 b4 b5 : ℂ) :
    schoberKernelT b1 b2 b3 b4 b5 =
      PowerSeries.X * schoberKernelR b1 b2 b3 b4 b5 := by
  unfold schoberKernelT schoberKernelR
  ring

private theorem schoberKernelR_const (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.constantCoeff (schoberKernelR b1 b2 b3 b4 b5) =
      schoberKernelT1 b1 b2 b3 := by
  simp [schoberKernelR]

private theorem schoberKernelR_coeff_one (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 1 (schoberKernelR b1 b2 b3 b4 b5) =
      schoberKernelT2 b2 b3 b4 := by
  simp [schoberKernelR, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_X]

private theorem schoberKernelQ3_outer_three (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 3 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      schoberKernelT3 b3 b4 b5 +
      schoberKernelT1 b1 b2 b3 * schoberKernelT2 b2 b3 b4 +
      PowerSeries.C ((3 : ℂ)⁻¹) * (schoberKernelT1 b1 b2 b3) ^ 3 := by
  let R := schoberKernelR b1 b2 b3 b4 b5
  let T := schoberKernelT b1 b2 b3 b4 b5
  have hT : T = PowerSeries.X * R := schoberKernelT_eq_X_mul_R _ _ _ _ _
  have hR0 : PowerSeries.constantCoeff R = schoberKernelT1 b1 b2 b3 :=
    schoberKernelR_const _ _ _ _ _
  have hR1 : PowerSeries.coeff 1 R = schoberKernelT2 b2 b3 b4 :=
    schoberKernelR_coeff_one _ _ _ _ _
  have hT3 : PowerSeries.coeff 3 T = schoberKernelT3 b3 b4 b5 :=
    schoberKernelT_outer_three _ _ _ _ _
  have hT2pow : PowerSeries.coeff 3 (T ^ 2) =
      2 * schoberKernelT1 b1 b2 b3 * schoberKernelT2 b2 b3 b4 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 1
    rw [PowerSeries.coeff_one_pow] at h
    calc
      _ = 2 * schoberKernelT2 b2 b3 b4 * schoberKernelT1 b1 b2 b3 := by
        simpa [hR0, hR1] using h
      _ = 2 * schoberKernelT1 b1 b2 b3 * schoberKernelT2 b2 b3 b4 := by ring
  have hT3pow : PowerSeries.coeff 3 (T ^ 3) =
      (schoberKernelT1 b1 b2 b3) ^ 3 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 3) 3 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  change PowerSeries.coeff 3
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3) = _
  have hhalf : (PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2 = 1 := by
    ext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · simp [PowerSeries.coeff_C, hn]
  simp [hT3, hT2pow, hT3pow]
  calc
    _ = ((PowerSeries.C ((2 : ℂ)⁻¹) : PowerSeries ℂ) * 2) *
        (schoberKernelT1 b1 b2 b3 * schoberKernelT2 b2 b3 b4) := by ring
    _ = _ := by rw [hhalf]; ring

private noncomputable def schoberInnerR1 (b1 b2 b3 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C b1 + PowerSeries.C b2 * PowerSeries.X +
    PowerSeries.C b3 * PowerSeries.X ^ 2
private noncomputable def schoberInnerR2 (b2 b3 b4 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C b2 + PowerSeries.C b3 * PowerSeries.X +
    PowerSeries.C b4 * PowerSeries.X ^ 2
private noncomputable def schoberInnerR3 (b3 b4 b5 : ℂ) : PowerSeries ℂ :=
  PowerSeries.C b3 + PowerSeries.C b4 * PowerSeries.X +
    PowerSeries.C b5 * PowerSeries.X ^ 2

private theorem schoberInnerT1_eq_X_mul_R1 (b1 b2 b3 : ℂ) :
    schoberKernelT1 b1 b2 b3 = PowerSeries.X * schoberInnerR1 b1 b2 b3 := by
  unfold schoberKernelT1 schoberInnerR1
  ring
private theorem schoberInnerT2_eq_X_mul_R2 (b2 b3 b4 : ℂ) :
    schoberKernelT2 b2 b3 b4 = PowerSeries.X * schoberInnerR2 b2 b3 b4 := by
  unfold schoberKernelT2 schoberInnerR2
  ring
private theorem schoberInnerT3_eq_X_mul_R3 (b3 b4 b5 : ℂ) :
    schoberKernelT3 b3 b4 b5 = PowerSeries.X * schoberInnerR3 b3 b4 b5 := by
  unfold schoberKernelT3 schoberInnerR3
  ring

/-- The decisive (3,3) coefficient of the finite logarithmic kernel. -/
theorem schoberKernelQ3_coeff_three_three (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 3 3 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      schoberQ33 b1 b2 b3 b5 := by
  let R1 := schoberInnerR1 b1 b2 b3
  let R2 := schoberInnerR2 b2 b3 b4
  let R3 := schoberInnerR3 b3 b4 b5
  have hR10 : PowerSeries.constantCoeff R1 = b1 := by simp [R1, schoberInnerR1]
  have hR11 : PowerSeries.coeff 1 R1 = b2 := by
    simp [R1, schoberInnerR1, PowerSeries.coeff_X]
  have hR20 : PowerSeries.constantCoeff R2 = b2 := by simp [R2, schoberInnerR2]
  have hR21 : PowerSeries.coeff 1 R2 = b3 := by
    simp [R2, schoberInnerR2, PowerSeries.coeff_X]
  have hR32 : PowerSeries.coeff 2 R3 = b5 := by
    simp [R3, schoberInnerR3, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  have hT3 : PowerSeries.coeff 3 (schoberKernelT3 b3 b4 b5) = b5 := by
    rw [schoberInnerT3_eq_X_mul_R3]
    simpa only [PowerSeries.coeff_succ_X_mul] using hR32
  have hT12 : PowerSeries.coeff 3
      (schoberKernelT1 b1 b2 b3 * schoberKernelT2 b2 b3 b4) =
        b1 * b3 + b2 ^ 2 := by
    rw [schoberInnerT1_eq_X_mul_R1, schoberInnerT2_eq_X_mul_R2]
    calc
      _ = PowerSeries.coeff 3 (PowerSeries.X ^ 2 * (R1 * R2)) := by
        congr 1
        ring
      _ = PowerSeries.coeff 1 (R1 * R2) :=
        PowerSeries.coeff_X_pow_mul (R1 * R2) 2 1
      _ = b1 * b3 + b2 ^ 2 := by
        rw [PowerSeries.coeff_one_mul]
        rw [hR10, hR11, hR20, hR21]
        ring
  have hT13 : PowerSeries.coeff 3 ((schoberKernelT1 b1 b2 b3) ^ 3) =
      b1 ^ 3 := by
    rw [schoberInnerT1_eq_X_mul_R1, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R1 ^ 3) 3 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR10] using h
  rw [schoberBiCoeff, schoberKernelQ3_outer_three]
  simp only [map_add]
  rw [hT3, hT12, PowerSeries.coeff_C_mul, hT13]
  simp [schoberQ33]
  ring

private theorem schoberKernelQ3_outer_two (b1 b2 b3 b4 b5 : ℂ) :
    PowerSeries.coeff 2 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      schoberKernelT2 b2 b3 b4 +
      PowerSeries.C ((2 : ℂ)⁻¹) * (schoberKernelT1 b1 b2 b3) ^ 2 := by
  let R := schoberKernelR b1 b2 b3 b4 b5
  let T := schoberKernelT b1 b2 b3 b4 b5
  have hT : T = PowerSeries.X * R := schoberKernelT_eq_X_mul_R _ _ _ _ _
  have hR0 : PowerSeries.constantCoeff R = schoberKernelT1 b1 b2 b3 :=
    schoberKernelR_const _ _ _ _ _
  have hT2 : PowerSeries.coeff 2 T = schoberKernelT2 b2 b3 b4 :=
    schoberKernelT_outer_two _ _ _ _ _
  have hT2pow : PowerSeries.coeff 2 (T ^ 2) =
      (schoberKernelT1 b1 b2 b3) ^ 2 := by
    rw [hT, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R ^ 2) 2 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR0] using h
  have hT3pow : PowerSeries.coeff 2 (T ^ 3) = 0 := by
    rw [hT, mul_pow]
    simpa using PowerSeries.coeff_X_pow_mul' (R ^ 3) 3 2
  change PowerSeries.coeff 2
      (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
        PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3) = _
  simp [hT2, hT2pow, hT3pow]

theorem schoberKernelQ3_coeff_two_two (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 2 2 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      schoberQ22 b1 b3 := by
  let R1 := schoberInnerR1 b1 b2 b3
  have hR10 : PowerSeries.constantCoeff R1 = b1 := by simp [R1, schoberInnerR1]
  have hT2 : PowerSeries.coeff 2 (schoberKernelT2 b2 b3 b4) = b3 := by
    rw [schoberInnerT2_eq_X_mul_R2]
    simp [schoberInnerR2, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_X]
  have hT1pow : PowerSeries.coeff 2 ((schoberKernelT1 b1 b2 b3) ^ 2) =
      b1 ^ 2 := by
    rw [schoberInnerT1_eq_X_mul_R1, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R1 ^ 2) 2 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR10] using h
  rw [schoberBiCoeff, schoberKernelQ3_outer_two]
  simp only [map_add]
  rw [hT2, PowerSeries.coeff_C_mul, hT1pow]
  simp only [schoberQ22]
  ring

theorem schoberKernelQ3_coeff_three_two (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 3 2 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      b4 + b1 * b2 := by
  let R1 := schoberInnerR1 b1 b2 b3
  have hR10 : PowerSeries.constantCoeff R1 = b1 := by
    simp [R1, schoberInnerR1]
  have hR11 : PowerSeries.coeff 1 R1 = b2 := by
    simp [R1, schoberInnerR1, PowerSeries.coeff_X_pow]
  have hT2 : PowerSeries.coeff 3 (schoberKernelT2 b2 b3 b4) = b4 := by
    simp [schoberKernelT2, PowerSeries.coeff_X_pow]
  have hT1pow : PowerSeries.coeff 3 ((schoberKernelT1 b1 b2 b3) ^ 2) =
      2 * b1 * b2 := by
    rw [schoberInnerT1_eq_X_mul_R1, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (R1 ^ 2) 2 1
    rw [show 2 + 1 = 3 by omega] at h
    rw [h, PowerSeries.coeff_one_pow]
    simp [PowerSeries.coeff_one_mul, hR10, hR11]
    ring
  rw [schoberBiCoeff, schoberKernelQ3_outer_two]
  simp only [map_add]
  rw [hT2, PowerSeries.coeff_C_mul, hT1pow]
  ring

theorem schoberKernelQ3_coeff_two_three (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 2 3 (schoberKernelQ3 b1 b2 b3 b4 b5) =
      b4 + b1 * b2 := by
  let R1 := schoberInnerR1 b1 b2 b3
  let R2 := schoberInnerR2 b2 b3 b4
  let T1 := schoberKernelT1 b1 b2 b3
  let T2 := schoberKernelT2 b2 b3 b4
  have hR10 : PowerSeries.constantCoeff R1 = b1 := by simp [R1, schoberInnerR1]
  have hR20 : PowerSeries.constantCoeff R2 = b2 := by simp [R2, schoberInnerR2]
  have hT3 : PowerSeries.coeff 2 (schoberKernelT3 b3 b4 b5) = b4 := by
    simp [schoberKernelT3, PowerSeries.coeff_X_pow]
  have hprod : PowerSeries.coeff 2 (T1 * T2) = b1 * b2 := by
    dsimp only [T1, T2]
    rw [schoberInnerT1_eq_X_mul_R1, schoberInnerT2_eq_X_mul_R2]
    have heq : (PowerSeries.X * R1) * (PowerSeries.X * R2) =
        PowerSeries.X ^ 2 * (R1 * R2) := by ring
    rw [heq]
    have h := PowerSeries.coeff_X_pow_mul (R1 * R2) 2 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hR10, hR20] using h
  have hcube : PowerSeries.coeff 2 (T1 ^ 3) = 0 := by
    dsimp only [T1]
    rw [schoberInnerT1_eq_X_mul_R1, mul_pow]
    simpa using PowerSeries.coeff_X_pow_mul' (R1 ^ 3) 3 2
  rw [schoberBiCoeff, schoberKernelQ3_outer_three]
  simp only [map_add]
  rw [hT3, hprod, PowerSeries.coeff_C_mul, hcube]
  ring

theorem schoberKernelQ3_coeff_one_one (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 1 1 (schoberKernelQ3 b1 b2 b3 b4 b5) = b1 := by
  rw [schoberBiCoeff, schoberKernelQ3_outer_one]
  simp [schoberKernelT1, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

theorem schoberKernelQ3_coeff_two_one (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 2 1 (schoberKernelQ3 b1 b2 b3 b4 b5) = b2 := by
  rw [schoberBiCoeff, schoberKernelQ3_outer_one]
  simp [schoberKernelT1, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

theorem schoberKernelQ3_coeff_three_one (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 3 1 (schoberKernelQ3 b1 b2 b3 b4 b5) = b3 := by
  rw [schoberBiCoeff, schoberKernelQ3_outer_one]
  simp [schoberKernelT1, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]

theorem schoberKernelQ3_coeff_one_two (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 1 2 (schoberKernelQ3 b1 b2 b3 b4 b5) = b2 := by
  have hT2 : PowerSeries.coeff 1 (schoberKernelT2 b2 b3 b4) = b2 := by
    simp [schoberKernelT2, PowerSeries.coeff_X_pow]
  have hT10 : PowerSeries.constantCoeff (schoberKernelT1 b1 b2 b3) = 0 := by
    simp [schoberKernelT1]
  have hsq : PowerSeries.coeff 1 ((schoberKernelT1 b1 b2 b3) ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, hT10]
  rw [schoberBiCoeff, schoberKernelQ3_outer_two]
  simp only [map_add]
  rw [hT2, PowerSeries.coeff_C_mul, hsq]
  simp

theorem schoberKernelQ3_coeff_one_three (b1 b2 b3 b4 b5 : ℂ) :
    schoberBiCoeff 1 3 (schoberKernelQ3 b1 b2 b3 b4 b5) = b3 := by
  let T1 := schoberKernelT1 b1 b2 b3
  let T2 := schoberKernelT2 b2 b3 b4
  have hT3 : PowerSeries.coeff 1 (schoberKernelT3 b3 b4 b5) = b3 := by
    simp [schoberKernelT3, PowerSeries.coeff_X_pow]
  have hT10 : PowerSeries.constantCoeff T1 = 0 := by simp [T1, schoberKernelT1]
  have hT20 : PowerSeries.constantCoeff T2 = 0 := by simp [T2, schoberKernelT2]
  have hprod : PowerSeries.coeff 1 (T1 * T2) = 0 := by
    simp [PowerSeries.coeff_one_mul, hT10, hT20]
  have hcube : PowerSeries.coeff 1 (T1 ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, hT10]
  rw [schoberBiCoeff, schoberKernelQ3_outer_three]
  simp only [map_add]
  rw [hT3, hprod, PowerSeries.coeff_C_mul, hcube]
  simp

/-- The three Schober contributions are exactly the low bidegree coefficients
of the finite logarithmic kernel. -/
theorem schoberFiniteContributions_eq_kernelCoefficients
    (b1 b2 b3 b4 b5 : ℂ) :
    schoberFiniteLinear b1 b2 b3 b5 =
        b1 ^ 2 * schoberBiCoeff 1 1 (schoberKernelQ3 b1 b2 b3 b4 b5) +
        b1 * (schoberBiCoeff 1 3 (schoberKernelQ3 b1 b2 b3 b4 b5) +
              schoberBiCoeff 3 1 (schoberKernelQ3 b1 b2 b3 b4 b5)) +
        schoberBiCoeff 3 3 (schoberKernelQ3 b1 b2 b3 b4 b5) ∧
      schoberFiniteQuadratic b1 b2 b3 =
        schoberBiCoeff 1 1 (schoberKernelQ3 b1 b2 b3 b4 b5) *
          schoberBiCoeff 2 2 (schoberKernelQ3 b1 b2 b3 b4 b5) +
        schoberBiCoeff 1 2 (schoberKernelQ3 b1 b2 b3 b4 b5) *
          schoberBiCoeff 2 1 (schoberKernelQ3 b1 b2 b3 b4 b5) ∧
      schoberFiniteCubic b1 =
        (schoberBiCoeff 1 1 (schoberKernelQ3 b1 b2 b3 b4 b5)) ^ 3 / 6 := by
  simp [schoberFiniteLinear, schoberFiniteQuadratic, schoberFiniteCubic,
    schoberQ11, schoberQ12, schoberQ13,
    schoberKernelQ3_coeff_one_one, schoberKernelQ3_coeff_two_one,
    schoberKernelQ3_coeff_three_one, schoberKernelQ3_coeff_one_two,
    schoberKernelQ3_coeff_one_three, schoberKernelQ3_coeff_two_two,
    schoberKernelQ3_coeff_three_three]
  constructor <;> ring
end SpringerLean