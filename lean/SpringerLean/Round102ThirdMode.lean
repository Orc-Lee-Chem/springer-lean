import SpringerLean.Round101KernelBridge

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- The missing fourth negative mode of the actual third Faber factor.
This uses the same `F` as its real analytic Taylor coefficient interface. -/
theorem thirdFaberFactor_actual_mode_seven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 7 =
      3 * (exteriorForwardCoeff F 6 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
        2 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 +
        exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2) := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hg (p : ℕ) : PowerSeries.coeff p g = exteriorForwardCoeff F (p + 1) := by
    simp [g, f, exteriorFormalForward_coeff]
  have hg0 : PowerSeries.constantCoeff g = b₁ := by
    simpa [b₁, PowerSeries.coeff_zero_eq_constantCoeff] using hg 0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [b₂] using hg 1
  have hsq : PowerSeries.coeff 3 (g ^ 2) =
      2 * b₁ * exteriorForwardCoeff F 4 +
      2 * b₂ * exteriorForwardCoeff F 3 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp only [hg]
    simp [hg0, b₁]
    ring
  have hcube : PowerSeries.coeff 1 (g ^ 3) = 3 * b₁ ^ 2 * b₂ := by
    rw [PowerSeries.coeff_one_pow]
    simp only [hg0, hg1]
    ring
  have hseries := thirdFaberFactor_actualTaylorSeries F hc
  rw [← actualTaylorSeries_coeff, hseries]
  change PowerSeries.coeff 7
    (φ ^ 3 - PowerSeries.C (3 * b₁) * PowerSeries.X ^ 2 * φ -
      PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3) = _
  have hform : φ ^ 3 - PowerSeries.C (3 * b₁) * PowerSeries.X ^ 2 * φ -
      PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3 =
      1 + PowerSeries.X ^ 2 * (3 * g - PowerSeries.C (3 * b₁)) -
      PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4 * (3 * g ^ 2 - PowerSeries.C (3 * b₁) * g) +
      PowerSeries.X ^ 6 * g ^ 3 := by
    rw [hφ]
    ring
  rw [hform]
  simp only [map_add, map_sub]
  have hfirst : PowerSeries.coeff 7 (1 : PowerSeries ℂ) = 0 := by simp
  have hsecond : PowerSeries.coeff 7
      (PowerSeries.X ^ 2 * (3 * g - PowerSeries.C (3 * b₁))) =
      3 * exteriorForwardCoeff F 6 := by
    rw [show 7 = 5 + 2 by omega, PowerSeries.coeff_X_pow_mul]
    simp [hg]
  have hthird : PowerSeries.coeff 7
      (PowerSeries.C (3 * b₂) * PowerSeries.X ^ 3) = 0 := by
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_assoc]
  have hfourth : PowerSeries.coeff 7
      (PowerSeries.X ^ 4 * (3 * g ^ 2 - PowerSeries.C (3 * b₁) * g)) =
      3 * (2 * b₁ * exteriorForwardCoeff F 4 +
          2 * b₂ * exteriorForwardCoeff F 3) -
      3 * b₁ * exteriorForwardCoeff F 4 := by
    rw [show 7 = 3 + 4 by omega, PowerSeries.coeff_X_pow_mul]
    simp [hsq, hg, PowerSeries.coeff_C_mul, mul_assoc]
  have hfifth : PowerSeries.coeff 7 (PowerSeries.X ^ 6 * g ^ 3) =
      3 * b₁ ^ 2 * b₂ := by
    rw [show 7 = 1 + 6 by omega, PowerSeries.coeff_X_pow_mul]
    exact hcube
  rw [hfirst, hsecond, hthird, hfourth, hfifth]
  dsimp only [b₁, b₂]
  ring

/-- The third actual Faber row's fourth column agrees with three times
the fourth-column coefficient of the same actual map's logarithmic kernel. -/
theorem thirdFaberFactor_actual_mode_seven_eq_logKernel4
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 7 =
      3 * schoberBiCoeff 4 3
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)) := by
  rw [thirdFaberFactor_actual_mode_seven F hc,
    schoberKernelQ4_coeff_four_three]

/-- The central degree-two entry of Q4 agrees with its paper coefficient. -/
theorem schoberKernelQ4_coeff_two_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 2 2 (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₃ + (2 : ℂ)⁻¹ * b₁ ^ 2 := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  have hR₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT4Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 2 (R₁ ^ 2) = b₁ ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₁₁]
    ring
  rw [schoberBiCoeff, schoberKernelQ4_outer_two]
  change PowerSeries.coeff 2 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]

theorem schoberKernelQ4_coeff_three_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 3 2 (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₄ + b₁ * b₂ := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  have hR₂ : PowerSeries.coeff 3 R₂ = b₄ := by
    simp [R₂, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT4Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hsq : PowerSeries.coeff 3 (R₁ ^ 2) = 2 * b₁ * b₂ := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₁₁, hR₁₂]
    ring
  rw [schoberBiCoeff, schoberKernelQ4_outer_two]
  change PowerSeries.coeff 3 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]
  ring

theorem schoberKernelQ4_coeff_two_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 2 3 (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₄ + b₁ * b₂ := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  have hR₃ : PowerSeries.coeff 2 R₃ = b₄ := by
    simp [R₃, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT4Row]
  have hR₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT4Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hprod : PowerSeries.coeff 2 (R₁ * R₂) = b₁ * b₂ := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₂₀, hR₁₁, hR₂₁]
  have hcube : PowerSeries.coeff 2 (R₁ ^ 3) = 0 := by
    let S := PowerSeries.C b₁ + PowerSeries.C b₂ * PowerSeries.X +
      PowerSeries.C b₃ * PowerSeries.X ^ 2 +
      PowerSeries.C b₄ * PowerSeries.X ^ 3
    have hR₁ : R₁ = PowerSeries.X * S := by
      dsimp [R₁, S, schoberKernelT4Row]
      ring
    rw [hR₁, mul_pow]
    simp [PowerSeries.coeff_X_pow_mul']
  rw [schoberBiCoeff, schoberKernelQ4_outer_three]
  change PowerSeries.coeff 2
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [hR₃, hprod, hcube]

theorem schoberKernelQ4_coeff_three_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 3 3 (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
      b₅ + b₁ * b₃ + b₂ ^ 2 + (3 : ℂ)⁻¹ * b₁ ^ 3 := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  have hR₃ : PowerSeries.coeff 3 R₃ = b₅ := by
    simp [R₃, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT4Row]
  have hR₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT4Row]
  have hR₁₁ : PowerSeries.coeff 1 R₁ = b₁ := by
    simp [R₁, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₂ : PowerSeries.coeff 2 R₁ = b₂ := by
    simp [R₁, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₂₁ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₂₂ : PowerSeries.coeff 2 R₂ = b₃ := by
    simp [R₂, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hprod : PowerSeries.coeff 3 (R₁ * R₂) = b₁ * b₃ + b₂ ^ 2 := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    simp [hR₁₀, hR₂₀, hR₁₁, hR₁₂, hR₂₁, hR₂₂]
    ring
  have hcube : PowerSeries.coeff 3 (R₁ ^ 3) = b₁ ^ 3 := by
    let S := PowerSeries.C b₁ + PowerSeries.C b₂ * PowerSeries.X +
      PowerSeries.C b₃ * PowerSeries.X ^ 2 +
      PowerSeries.C b₄ * PowerSeries.X ^ 3
    have hR₁ : R₁ = PowerSeries.X * S := by
      dsimp [R₁, S, schoberKernelT4Row]
      ring
    have hS₀ : PowerSeries.constantCoeff S = b₁ := by
      simp [S]
    rw [hR₁, mul_pow]
    have h := PowerSeries.coeff_X_pow_mul (S ^ 3) 3 0
    simpa [PowerSeries.coeff_zero_eq_constantCoeff, hS₀] using h
  rw [schoberBiCoeff, schoberKernelQ4_outer_three]
  change PowerSeries.coeff 3
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [hR₃, hprod, hcube]
  ring

theorem schoberKernelQ4_coeff_one_two
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 1 2 (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) = b₂ := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  have hR₂ : PowerSeries.coeff 1 R₂ = b₂ := by
    simp [R₂, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT4Row]
  have hsq : PowerSeries.coeff 1 (R₁ ^ 2) = 0 := by
    simp [PowerSeries.coeff_one_pow, hR₁₀]
  rw [schoberBiCoeff, schoberKernelQ4_outer_two]
  change PowerSeries.coeff 1 (R₂ + PowerSeries.C ((2 : ℂ)⁻¹) * R₁ ^ 2) = _
  simp [hR₂, hsq]

theorem schoberKernelQ4_coeff_one_three
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) :
    schoberBiCoeff 1 3 (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) = b₃ := by
  let R₁ := schoberKernelT4Row b₁ b₂ b₃ b₄
  let R₂ := schoberKernelT4Row b₂ b₃ b₄ b₅
  let R₃ := schoberKernelT4Row b₃ b₄ b₅ b₆
  have hR₃ : PowerSeries.coeff 1 R₃ = b₃ := by
    simp [R₃, schoberKernelT4Row, PowerSeries.coeff_X_pow]
  have hR₁₀ : PowerSeries.constantCoeff R₁ = 0 := by
    simp [R₁, schoberKernelT4Row]
  have hR₂₀ : PowerSeries.constantCoeff R₂ = 0 := by
    simp [R₂, schoberKernelT4Row]
  have hprod : PowerSeries.coeff 1 (R₁ * R₂) = 0 := by
    simp [PowerSeries.coeff_one_mul, hR₁₀, hR₂₀]
  have hcube : PowerSeries.coeff 1 (R₁ ^ 3) = 0 := by
    simp [PowerSeries.coeff_one_pow, hR₁₀]
  rw [schoberBiCoeff, schoberKernelQ4_outer_three]
  change PowerSeries.coeff 1
    (R₃ + R₁ * R₂ + PowerSeries.C ((3 : ℂ)⁻¹) * R₁ ^ 3) = _
  simp [hR₃, hprod, hcube]

/-- All nine low entries of the degree-four kernel agree with the earlier
degree-three kernel, with no assumption on the forward coefficients. -/
theorem schoberKernelQ4_low_block_eq_Q3
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ : ℂ) (i j : Fin 3) :
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) =
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ3 b₁ b₂ b₃ b₄ b₅) := by
  obtain ⟨h11, h21, h31⟩ :=
    schoberKernelQ4_first_row_low b₁ b₂ b₃ b₄ b₅ b₆ b₇
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      Nat.zero_add, Nat.reduceAdd] <;>
    simp [h11, h21, h31,
      schoberKernelQ4_coeff_one_two, schoberKernelQ4_coeff_one_three,
      schoberKernelQ4_coeff_two_two, schoberKernelQ4_coeff_three_two,
      schoberKernelQ4_coeff_two_three, schoberKernelQ4_coeff_three_three,
      schoberKernelQ3_coeff_one_one, schoberKernelQ3_coeff_two_one,
      schoberKernelQ3_coeff_three_one, schoberKernelQ3_coeff_one_two,
      schoberKernelQ3_coeff_two_two, schoberKernelQ3_coeff_three_two,
      schoberKernelQ3_coeff_one_three, schoberKernelQ3_coeff_two_three,
      schoberKernelQ3_coeff_three_three, schoberQ22, schoberQ33] <;>
    ring

/-- All four actual second-Faber row entries agree with the Q4 kernel. -/
theorem fourthActualFaberMode_second_row_eq_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : Fin 4) :
    fourthActualFaberMode F 1 j =
      2 * schoberBiCoeff (j.val + 1) 2
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)) := by
  rcases secondFaberFactor_actual_modes_eq_logKernel F hc with ⟨h3, h4, h5⟩
  fin_cases j
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 3 = _
    rw [schoberKernelQ3_coeff_two_one] at h3
    rw [schoberKernelQ4_coeff_one_two]
    exact h3
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 4 = _
    rw [schoberKernelQ3_coeff_two_two] at h4
    rw [schoberKernelQ4_coeff_two_two]
    simp only [schoberQ22, div_eq_mul_inv] at h4
    convert h4 using 1 <;> ring
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 5 = _
    rw [schoberKernelQ3_coeff_two_three] at h5
    rw [schoberKernelQ4_coeff_three_two]
    exact h5
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) 6 = _
    exact secondFaberFactor_actual_mode_six_eq_logKernel4 F hc

/-- All four actual third-Faber row entries agree with the Q4 kernel. -/
theorem fourthActualFaberMode_third_row_eq_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : Fin 4) :
    fourthActualFaberMode F 2 j =
      3 * schoberBiCoeff (j.val + 1) 3
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)) := by
  rcases thirdFaberFactor_actual_modes_eq_logKernel F hc with ⟨h4, h5, h6⟩
  fin_cases j
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 4 = _
    rw [schoberKernelQ3_coeff_three_one] at h4
    rw [schoberKernelQ4_coeff_one_three]
    exact h4
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 5 = _
    rw [schoberKernelQ3_coeff_three_two] at h5
    rw [schoberKernelQ4_coeff_two_three]
    exact h5
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 6 = _
    rw [schoberKernelQ3_coeff_three_three] at h6
    rw [schoberKernelQ4_coeff_three_three]
    simp only [schoberQ33, div_eq_mul_inv] at h6
    convert h6 using 1 <;> ring
  · change actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) 7 = _
    exact thirdFaberFactor_actual_mode_seven_eq_logKernel4 F hc

theorem fourthActualFaberMode_fourth_row_eq_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : Fin 4) :
    fourthActualFaberMode F 3 j =
      4 * schoberBiCoeff (j.val + 1) 4
        (schoberKernelQ4
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7)) := by
  rcases fourthFaberFactor_actual_modes_eq_logKernel4 F hc with ⟨h5, h6, h7, h8⟩
  fin_cases j
  · change actualTaylorCoeff (fourthFaberFactor F) 5 = _
    exact h5
  · change actualTaylorCoeff (fourthFaberFactor F) 6 = _
    exact h6
  · change actualTaylorCoeff (fourthFaberFactor F) 7 = _
    exact h7
  · change actualTaylorCoeff (fourthFaberFactor F) 8 = _
    exact h8

/-- The complete sixteen-entry bridge from the independently Taylor-read
actual Faber matrix of the same map to its finite logarithmic kernel. -/
theorem fourthActualFaberMode_eq_logKernel4
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (i j : Fin 4) :
    fourthActualFaberMode F i j =
      ((i.val + 1 : ℕ) : ℂ) *
        schoberBiCoeff (j.val + 1) (i.val + 1)
          (schoberKernelQ4
            (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
            (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
            (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
            (exteriorForwardCoeff F 7)) := by
  fin_cases i
  · simpa [fourthActualFaberMode] using
      fourthActualFaberMode_first_row_eq_kernel F hc j
  · simpa [fourthActualFaberMode] using
      fourthActualFaberMode_second_row_eq_kernel F hc j
  · simpa [fourthActualFaberMode] using
      fourthActualFaberMode_third_row_eq_kernel F hc j
  · simpa [fourthActualFaberMode] using
      fourthActualFaberMode_fourth_row_eq_kernel F hc j

/-- The actual-map weighted Faber-area inequality, now expressed entirely
with all sixteen coefficients of the degree-four logarithmic kernel. -/
theorem exterior_schoberKernelQ4_weighted_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 4 → ℂ) :
    (∑ j : Fin 4,
      ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 4,
          α i * ((i.val + 1 : ℕ) : ℂ) *
            schoberBiCoeff (j.val + 1) (i.val + 1)
              (schoberKernelQ4
                (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
                (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
                (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
                (exteriorForwardCoeff F 7))‖ ^ 2) ≤
      ∑ i : Fin 4, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  have h := exterior_fourthActualFaberMode_weighted_contraction F hc α
  simpa only [fourthActualFaberMode_eq_logKernel4 F hc, mul_assoc] using h

end SpringerLean
