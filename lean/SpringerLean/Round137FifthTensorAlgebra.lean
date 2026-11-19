import SpringerLean.Round136FifthTensorBound

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace SpringerLean

theorem schoberFifthTensorTerm5_eq_firstCoeff_pow_five (F : ℂ → ℂ) :
    schoberFifthTensorTerm5 F = (exteriorForwardCoeff F 1) ^ 5 := by
  simp [schoberFifthTensorTerm5, schoberFifthV5, schoberFifthL,
    schoberActualC5Tensor5, schoberActualC5Tensor4,
    schoberActualC5Tensor3, schoberActualC5Tensor2,
    Fintype.sum_prod_type, Fin.sum_univ_five,
    schoberActualC5, schoberBiCoeff, schoberKernelQ5_outer_one,
    schoberKernelT5Row, PowerSeries.coeff_X_pow]
  ring

theorem schoberFifthTensorTerm4_eq_forward (F : ℂ → ℂ) :
    schoberFifthTensorTerm4 F =
      4 * (exteriorForwardCoeff F 1) ^ 3 * exteriorForwardCoeff F 3 +
      12 * (exteriorForwardCoeff F 1) ^ 2 *
        (exteriorForwardCoeff F 2) ^ 2 +
      2 * (exteriorForwardCoeff F 1) ^ 5 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₅ := exteriorForwardCoeff F 5
  let b₆ := exteriorForwardCoeff F 6
  let b₇ := exteriorForwardCoeff F 7
  let b₈ := exteriorForwardCoeff F 8
  let b₉ := exteriorForwardCoeff F 9
  let Q := schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h12 : PowerSeries.coeff 1 (PowerSeries.coeff 2 Q) = b₂ := by
    exact schoberKernelQ5_coeff_one_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h22 : PowerSeries.coeff 2 (PowerSeries.coeff 2 Q) =
      b₃ + (1 / 2 : ℂ) * b₁ ^ 2 := by
    change schoberBiCoeff 2 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = _
    simpa only [one_div] using
      schoberKernelQ5_coeff_two_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  simp [schoberFifthTensorTerm4, schoberFifthV4, schoberFifthL,
    schoberActualC5Tensor4, schoberActualC5Tensor3,
    schoberActualC5Tensor2, Fintype.sum_prod_type, Fin.sum_univ_five,
    schoberActualC5, schoberBiCoeff, schoberKernelQ5_outer_one,
    schoberKernelT5Row, PowerSeries.coeff_X_pow]
  rw [h12, h22]
  simp only [one_add_one_eq_two]
  have hs : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  field_simp [hs]
  norm_num [Real.sq_sqrt] at *
  ring

theorem schoberFifthTensorTerm3_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFifthTensorTerm3 F =
      12 * (exteriorForwardCoeff F 2) ^ 2 * exteriorForwardCoeff F 3 +
      9 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 3) ^ 2 +
      12 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 4 +
      3 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 5 +
      36 * (exteriorForwardCoeff F 1) ^ 2 *
        (exteriorForwardCoeff F 2) ^ 2 +
      24 * (exteriorForwardCoeff F 1) ^ 3 * exteriorForwardCoeff F 3 +
      (43 / 4 : ℂ) * (exteriorForwardCoeff F 1) ^ 5 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₅ := exteriorForwardCoeff F 5
  let b₆ := exteriorForwardCoeff F 6
  let b₇ := exteriorForwardCoeff F 7
  let b₈ := exteriorForwardCoeff F 8
  let b₉ := exteriorForwardCoeff F 9
  let Q := schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h12 : PowerSeries.coeff 1 (PowerSeries.coeff 2 Q) = b₂ := by
    exact schoberKernelQ5_coeff_one_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h13 : PowerSeries.coeff 1 (PowerSeries.coeff 3 Q) = b₃ := by
    exact schoberKernelQ5_coeff_one_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h22 : PowerSeries.coeff 2 (PowerSeries.coeff 2 Q) =
      b₃ + (1 / 2 : ℂ) * b₁ ^ 2 := by
    change schoberBiCoeff 2 2
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) = _
    simpa only [one_div] using
      schoberKernelQ5_coeff_two_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h23 : PowerSeries.coeff 2 (PowerSeries.coeff 3 Q) =
      b₄ + b₁ * b₂ := by
    exact schoberKernelQ5_coeff_two_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h32 : PowerSeries.coeff 3 (PowerSeries.coeff 2 Q) =
      b₄ + b₁ * b₂ := by
    exact schoberKernelQ5_coeff_three_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h33 : PowerSeries.coeff 3 (PowerSeries.coeff 3 Q) =
      b₅ + b₁ * b₃ + b₂ ^ 2 + (3 : ℂ)⁻¹ * b₁ ^ 3 := by
    exact schoberKernelQ5_coeff_three_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  unfold schoberFifthTensorTerm3
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc]
  simp [schoberFifthTensorTerm3, schoberFifthV3, schoberFifthL,
    schoberActualC5Tensor3, schoberActualC5Tensor2,
    Fintype.sum_prod_type, Fin.sum_univ_five,
    schoberActualC5, schoberBiCoeff, schoberKernelQ5_outer_one,
    schoberKernelT5Row, PowerSeries.coeff_X_pow]
  rw [h12, h13, h22, h23, h32, h33]
  norm_num only [Nat.reduceAdd]
  have hs2 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hs3 : (Real.sqrt (3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  field_simp [hs2, hs3]
  norm_num [Real.sq_sqrt] at *
  ring

theorem schoberFifthTensorTerm1_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFifthTensorTerm1 F =
      exteriorForwardCoeff F 9 +
      2 * exteriorForwardCoeff F 4 ^ 2 +
      5 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
      6 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
      7 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
      16 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 3 +
      16 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 ^ 2 +
      32 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 4 +
      20 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 5 +
      40 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 ^ 2 +
      32 * exteriorForwardCoeff F 1 ^ 3 * exteriorForwardCoeff F 3 +
      (36 / 5 : ℂ) * exteriorForwardCoeff F 1 ^ 5 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₅ := exteriorForwardCoeff F 5
  let b₆ := exteriorForwardCoeff F 6
  let b₇ := exteriorForwardCoeff F 7
  let b₈ := exteriorForwardCoeff F 8
  let b₉ := exteriorForwardCoeff F 9
  let Q := schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h12 := schoberKernelQ5_coeff_one_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 1 (PowerSeries.coeff 2 Q) = _ at h12
  have h22 := schoberKernelQ5_coeff_two_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 2 (PowerSeries.coeff 2 Q) = _ at h22
  have h32 := schoberKernelQ5_coeff_three_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 3 (PowerSeries.coeff 2 Q) = _ at h32
  have h52 := schoberKernelQ5_coeff_five_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 5 (PowerSeries.coeff 2 Q) = _ at h52
  have h13 := schoberKernelQ5_coeff_one_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 1 (PowerSeries.coeff 3 Q) = _ at h13
  have h23 := schoberKernelQ5_coeff_two_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 2 (PowerSeries.coeff 3 Q) = _ at h23
  have h33 := schoberKernelQ5_coeff_three_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 3 (PowerSeries.coeff 3 Q) = _ at h33
  have h53 := schoberKernelQ5_coeff_five_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 5 (PowerSeries.coeff 3 Q) = _ at h53
  have h15 := schoberKernelQ5_coeff_one_five b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 1 (PowerSeries.coeff 5 Q) = _ at h15
  have h25 := schoberKernelQ5_coeff_two_five b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 2 (PowerSeries.coeff 5 Q) = _ at h25
  have h35 := schoberKernelQ5_coeff_three_five b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 3 (PowerSeries.coeff 5 Q) = _ at h35
  have h55 := schoberKernelQ5_coeff_five_five b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 5 (PowerSeries.coeff 5 Q) = _ at h55
  unfold schoberFifthTensorTerm1
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
    exteriorInverseCoeff_two_eq_forwardCoeff_two F hc,
    exteriorInverseCoeff_three_eq_forward F hc]
  simp [schoberFifthV1, schoberFifthL,
    Fin.sum_univ_five, schoberActualC5,
    schoberBiCoeff, schoberKernelQ5_outer_one,
    schoberKernelT5Row, PowerSeries.coeff_X_pow]
  rw [h12, h22, h32, h52, h13, h23, h33, h53,
    h15, h25, h35, h55]
  norm_num only [Nat.reduceAdd]
  have hs2 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hs3 : (Real.sqrt (3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  have hs5 : (Real.sqrt (5 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 5))
  field_simp [hs2, hs3, hs5]
  norm_num [Real.sq_sqrt] at *
  ring

theorem schoberFifthTensorTerm2_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberFifthTensorTerm2 F =
      4 * exteriorForwardCoeff F 4 ^ 2 +
      6 * exteriorForwardCoeff F 3 * exteriorForwardCoeff F 5 +
      4 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 6 +
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 7 +
      20 * exteriorForwardCoeff F 2 ^ 2 * exteriorForwardCoeff F 3 +
      21 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 ^ 2 +
      44 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 *
        exteriorForwardCoeff F 4 +
      15 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 5 +
      75 * exteriorForwardCoeff F 1 ^ 2 * exteriorForwardCoeff F 2 ^ 2 +
      (119 / 3 : ℂ) * exteriorForwardCoeff F 1 ^ 3 *
        exteriorForwardCoeff F 3 +
      (59 / 6 : ℂ) * exteriorForwardCoeff F 1 ^ 5 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  let b₄ := exteriorForwardCoeff F 4
  let b₅ := exteriorForwardCoeff F 5
  let b₆ := exteriorForwardCoeff F 6
  let b₇ := exteriorForwardCoeff F 7
  let b₈ := exteriorForwardCoeff F 8
  let b₉ := exteriorForwardCoeff F 9
  let Q := schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  have h12 := schoberKernelQ5_coeff_one_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 1 (PowerSeries.coeff 2 Q) = _ at h12
  have h22 := schoberKernelQ5_coeff_two_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 2 (PowerSeries.coeff 2 Q) = _ at h22
  have h32 := schoberKernelQ5_coeff_three_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 3 (PowerSeries.coeff 2 Q) = _ at h32
  have h42 := schoberKernelQ5_coeff_four_two b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 4 (PowerSeries.coeff 2 Q) = _ at h42
  have h13 := schoberKernelQ5_coeff_one_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 1 (PowerSeries.coeff 3 Q) = _ at h13
  have h23 := schoberKernelQ5_coeff_two_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 2 (PowerSeries.coeff 3 Q) = _ at h23
  have h33 := schoberKernelQ5_coeff_three_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 3 (PowerSeries.coeff 3 Q) = _ at h33
  have h43 := schoberKernelQ5_coeff_four_three b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 4 (PowerSeries.coeff 3 Q) = _ at h43
  have h14 := schoberKernelQ5_coeff_one_four b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 1 (PowerSeries.coeff 4 Q) = _ at h14
  have h24 := schoberKernelQ5_coeff_two_four b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 2 (PowerSeries.coeff 4 Q) = _ at h24
  have h34 := schoberKernelQ5_coeff_three_four b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 3 (PowerSeries.coeff 4 Q) = _ at h34
  have h44 := schoberKernelQ5_coeff_four_four b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  change PowerSeries.coeff 4 (PowerSeries.coeff 4 Q) = _ at h44
  unfold schoberFifthTensorTerm2
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc,
    exteriorInverseCoeff_two_eq_forwardCoeff_two F hc,
    exteriorInverseCoeff_three_eq_forward F hc]
  simp [schoberFifthV2, schoberFifthL,
    schoberActualC5Tensor2, Fintype.sum_prod_type,
    Fin.sum_univ_five, schoberActualC5, schoberBiCoeff,
    schoberKernelQ5_outer_one, schoberKernelT5Row,
    PowerSeries.coeff_X_pow]
  rw [h12, h22, h32, h42, h13, h23, h33, h43,
    h14, h24, h34, h44]
  norm_num only [Nat.reduceAdd]
  have hs2 : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hs3 : (Real.sqrt (3 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
  have hs6 : (Real.sqrt (6 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 6))
  field_simp [hs2, hs3, hs6]
  norm_num [Real.sq_sqrt] at *
  ring

/-- The finite logarithmic kernel tensor diagonal reads the independently
defined ninth actual inverse coefficient of the same exterior map. -/
theorem exteriorInverseCoeff_nine_eq_fifthTensorPolynomial
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 9 = schoberFifthTensorPolynomial F := by
  rw [exteriorInverseCoeff_nine_eq_forward F hc]
  unfold schoberFifthTensorPolynomial
  rw [schoberFifthTensorTerm1_eq_forward F hc,
    schoberFifthTensorTerm2_eq_forward F hc,
    schoberFifthTensorTerm3_eq_forward F hc,
    schoberFifthTensorTerm4_eq_forward F,
    schoberFifthTensorTerm5_eq_firstCoeff_pow_five F]
  ring

/-- The fifth Schober diagonal estimate, now without extra algebraic or
matrix assumptions. -/
theorem exteriorInverseCoeff_nine_norm_le_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 9‖ ≤ schoberActualDiagonal F 5 := by
  rw [exteriorInverseCoeff_nine_eq_fifthTensorPolynomial F hc]
  exact schoberFifthTensorPolynomial_norm_le_diagonal F hc

theorem exteriorInverseCoeff_nine_norm_le_fourteen
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorInverseCoeff F 9‖ ≤ 14 :=
  exteriorInverseCoeff_nine_norm_le_fourteen_of_diagonal F hc
    (exteriorInverseCoeff_nine_norm_le_diagonal F hc)

theorem exteriorInverseCoeff_nine_norm_lt_fourteen
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    ‖exteriorInverseCoeff F 9‖ < 14 :=
  exteriorInverseCoeff_nine_norm_lt_fourteen_of_diagonal F hc
    (exteriorInverseCoeff_nine_norm_le_diagonal F hc) hβ

theorem exteriorInverseCoeff_nine_norm_eq_fourteen_iff_slit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (‖exteriorInverseCoeff F 9‖ = 14 ↔
      ∃ a : ℂ, ‖a‖ = 1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :=
  exteriorInverseCoeff_nine_norm_eq_fourteen_iff_slit_of_diagonal F hc
    (exteriorInverseCoeff_nine_norm_le_diagonal F hc)

end SpringerLean
