import SpringerLean.Round169SixFaberFirstMode

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Every outer coefficient has zero inner constant term. -/
def schoberInnerConstantZero (A : PowerSeries (PowerSeries ℂ)) : Prop :=
  ∀ n : ℕ, PowerSeries.constantCoeff (PowerSeries.coeff n A) = 0

theorem schoberInnerConstantZero_mul
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (hB : schoberInnerConstantZero B) :
    schoberInnerConstantZero (A * B) := by
  intro n
  simp only [schoberInnerConstantZero] at hA hB
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [hA, hB]

theorem schoberInnerConstantZero_pow
    {A : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A) (k : ℕ) (hk : 1 ≤ k) :
    schoberInnerConstantZero (A ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  induction m with
  | zero => simpa using hA
  | succ m ih =>
    rw [pow_succ]
    exact schoberInnerConstantZero_mul (ih (by omega)) hA

theorem schoberBiCoeff_one_mul_of_innerConstantZero
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (hB : schoberInnerConstantZero B) (n : ℕ) :
    schoberBiCoeff 1 n (A * B) = 0 := by
  simp only [schoberInnerConstantZero] at hA hB
  unfold schoberBiCoeff
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [PowerSeries.coeff_one_mul, hA, hB]

theorem schoberBiCoeff_one_pow_eq_zero
    {A : PowerSeries (PowerSeries ℂ)}
    (hA : schoberInnerConstantZero A)
    (k n : ℕ) (hk : 2 ≤ k) :
    schoberBiCoeff 1 n (A ^ k) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show A ^ (2 + m) = A * A ^ (m + 1) by ring]
  exact schoberBiCoeff_one_mul_of_innerConstantZero hA
    (schoberInnerConstantZero_pow hA (m + 1) (by omega)) n

/-- Each quotient-correction row begins with a positive inner power. -/
private theorem schoberKernelT6Row_const_zero
    (a b c d e f : ℂ) :
    PowerSeries.constantCoeff (schoberKernelT6Row a b c d e f) = 0 := by
  simp [schoberKernelT6Row]

theorem schoberKernelT6_inner_constant_zero
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberInnerConstantZero
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) := by
  intro n
  simp [schoberKernelT6, PowerSeries.coeff_X_pow_mul',
    schoberKernelT6Row_const_zero]
  split_ifs <;> simp [schoberKernelT6Row_const_zero]

/-- The inner-linear term of the outer sixth quotient correction is the
actual forward coefficient in slot six. -/
theorem schoberKernelT6_coeff_one_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 1 6
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) = b₆ := by
  let R := schoberKernelOuterR6
    b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hR5 : PowerSeries.coeff 5 R =
      schoberKernelT6Row b₆ b₇ b₈ b₉ b₁₀ b₁₁ := by
    simp [R, schoberKernelOuterR6, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X]
  rw [schoberBiCoeff,
    schoberKernelT6_eq_X_mul_outerR6,
    show PowerSeries.coeff 6 (PowerSeries.X * R) =
      PowerSeries.coeff 5 R by
        simpa only [pow_one] using PowerSeries.coeff_X_pow_mul R 1 5]
  rw [hR5]
  simp [schoberKernelT6Row, PowerSeries.coeff_X_pow]

/-- At every outer order, the inner-linear logarithmic coefficient is the
inner-linear quotient-correction coefficient. -/
theorem schoberKernelQ6_inner_linear_eq_T6
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) (n : ℕ) :
    schoberBiCoeff 1 n
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) =
    schoberBiCoeff 1 n
      (schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) := by
  let T := schoberKernelT6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hT : schoberInnerConstantZero T :=
    schoberKernelT6_inner_constant_zero
      b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁
  have hp (k : ℕ) (hk : 2 ≤ k) : schoberBiCoeff 1 n (T ^ k) = 0 :=
    schoberBiCoeff_one_pow_eq_zero hT k n hk
  change schoberBiCoeff 1 n
    (T + PowerSeries.C (PowerSeries.C ((2 : ℂ)⁻¹)) * T ^ 2 +
      PowerSeries.C (PowerSeries.C ((3 : ℂ)⁻¹)) * T ^ 3 +
      PowerSeries.C (PowerSeries.C ((4 : ℂ)⁻¹)) * T ^ 4 +
      PowerSeries.C (PowerSeries.C ((5 : ℂ)⁻¹)) * T ^ 5 +
      PowerSeries.C (PowerSeries.C ((6 : ℂ)⁻¹)) * T ^ 6) =
    schoberBiCoeff 1 n T
  simp only [schoberBiCoeff] at hp
  simp [schoberBiCoeff, PowerSeries.coeff_C_mul, hp]

/-- The opposite corner of the new sixth row has the expected coefficient. -/
theorem schoberKernelQ6_coeff_one_six
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁ : ℂ) :
    schoberBiCoeff 1 6
      (schoberKernelQ6 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ b₁₀ b₁₁) = b₆ := by
  rw [schoberKernelQ6_inner_linear_eq_T6,
    schoberKernelT6_coeff_one_six]

end SpringerLean
