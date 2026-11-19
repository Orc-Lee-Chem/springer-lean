import SpringerLean.Round141SixthArithmetic
import SpringerLean.Round91MatrixNormalization

namespace SpringerLean

/-- The seventh comparison diagonal has a strict endpoint deficit. This
is a theorem about the actual inverse coefficients, independent of the
still separate principal kernel-to-diagonal inequality for B13. -/
theorem schoberActualDiagonal_seven_param_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 7 ≤
      80 + 52 * ‖exteriorForwardCoeff F 1‖ ^ 2 := by
  let β : ℝ := ‖exteriorForwardCoeff F 1‖
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hβ1 : β ≤ 1 := exteriorForwardCoeff_one_norm_le_of_finite_area F
    (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hβsq : β ^ 2 ≤ 1 := by nlinarith
  have hβcube : β ^ 3 ≤ β ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hβ1)]
  have hB1 := exteriorInverseCoeff_one_eq_forwardCoeff_one F hc
  have hB2 := exteriorInverseCoeff_two_eq_forwardCoeff_two F hc
  have hB4 := exteriorInverseCoeff_four_eq_forward F hc
  have hB3 := exteriorInverseCoeff_three_norm_le_one F hc
  have hB5 := exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq F hc
  have htail := exteriorForwardCoeff_finite_area_tail F hc 2 (by omega)
  norm_num [Finset.sum_Icc_succ_top] at htail
  have hB2sq : 2 * ‖exteriorInverseCoeff F 2‖ ^ 2 ≤ 1 - β ^ 2 := by
    simpa only [hB2] using htail
  have hfirst : ‖exteriorInverseCoeff F 5 +
      2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
      (exteriorInverseCoeff F 2) ^ 2 + (exteriorInverseCoeff F 1) ^ 3‖ ≤ 5 := by
    have htri := norm_add_le
      (exteriorInverseCoeff F 5 + 2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
        (exteriorInverseCoeff F 2) ^ 2) ((exteriorInverseCoeff F 1) ^ 3)
    have htri2 := norm_add_le
      (exteriorInverseCoeff F 5 + 2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3)
      ((exteriorInverseCoeff F 2) ^ 2)
    have htri3 := norm_add_le (exteriorInverseCoeff F 5)
      (2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3)
    simp only [norm_mul, norm_pow, hB1, Complex.norm_ofNat] at htri htri2 htri3
    have hprod : 2 * β * ‖exteriorInverseCoeff F 3‖ ≤ 2 * β := by
      nlinarith
    rw [hB1]
    dsimp only [β] at hβ0 hβ1 hβsq hβcube hB2sq hprod ⊢
    nlinarith
  have hfirstsq : ‖exteriorInverseCoeff F 5 +
      2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
      (exteriorInverseCoeff F 2) ^ 2 + (exteriorInverseCoeff F 1) ^ 3‖ ^ 2 ≤ 25 := by
    nlinarith [norm_nonneg (exteriorInverseCoeff F 5 +
      2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
      (exteriorInverseCoeff F 2) ^ 2 + (exteriorInverseCoeff F 1) ^ 3)]
  let weights : ℕ → ℂ := fun j =>
    if j = 2 then 12 * exteriorForwardCoeff F 1 else if j = 4 then 2 else 0
  have hpair := exteriorForwardCoeff_weighted_linear_combination_sq_le
    F hc 4 (by omega) weights
  norm_num [weights, Finset.sum_Icc_succ_top, norm_mul] at hpair
  have hsecond : ‖2 * exteriorInverseCoeff F 4 +
      6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2‖ ^ 2 ≤
      (1 + 72 * β ^ 2) * (1 - β ^ 2) := by
    rw [hB1, hB2, hB4]
    convert hpair using 1 <;> (try dsimp only [β]) <;> ring
  have hthird : ‖3 * exteriorInverseCoeff F 3 +
      6 * (exteriorInverseCoeff F 1) ^ 2‖ ≤ 3 + 6 * β ^ 2 := by
    calc
      _ ≤ ‖(3 : ℂ) * exteriorInverseCoeff F 3‖ +
          ‖(6 : ℂ) * (exteriorInverseCoeff F 1) ^ 2‖ := norm_add_le _ _
      _ = 3 * ‖exteriorInverseCoeff F 3‖ + 6 * β ^ 2 := by
        simp [hB1, β, norm_mul, norm_pow]
      _ ≤ _ := by linarith
  have hthirdsq : ‖3 * exteriorInverseCoeff F 3 +
      6 * (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 ≤ (3 + 6 * β ^ 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hthird
  rw [schoberActualDiagonal_seven F hc, hB1]
  rw [hB1] at hfirstsq hsecond hthirdsq
  dsimp only [β] at hβsq hB2sq hsecond hthirdsq ⊢
  nlinarith [sq_nonneg (1 - ‖exteriorForwardCoeff F 1‖ ^ 2)]

theorem schoberActualDiagonal_seven_lt_of_interior
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    schoberActualDiagonal F 7 < 132 := by
  have h := schoberActualDiagonal_seven_param_le F hc
  nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]

end SpringerLean
