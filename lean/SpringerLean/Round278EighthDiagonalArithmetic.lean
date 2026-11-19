import SpringerLean.Round277SixthInverseCoefficient
import SpringerLean.Round273SeventhDiagonalArithmetic

namespace SpringerLean

theorem schoberActualDiagonal_eight_param_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 8 ≤
      (2227 + 347 * ‖exteriorForwardCoeff F 1‖ ^ 2) / 6 := by
  let β : ℝ := ‖exteriorForwardCoeff F 1‖
  let y : ℝ := β ^ 2
  have hβ0 : 0 ≤ β := norm_nonneg _
  have hβ1 : β ≤ 1 := exteriorForwardCoeff_one_norm_le_of_finite_area F
    (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hy0 : 0 ≤ y := sq_nonneg _
  have hy1 : y ≤ 1 := by dsimp [y]; nlinarith
  have hcube : β ^ 3 ≤ y := by
    dsimp [y]
    nlinarith [mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hβ1)]
  have hβlin : 2 * β ≤ 1 + y := by dsimp [y]; nlinarith [sq_nonneg (1 - β)]
  have hB1 := exteriorInverseCoeff_one_eq_forwardCoeff_one F hc
  have hB2 := exteriorInverseCoeff_two_eq_forwardCoeff_two F hc
  have hB3eq := exteriorInverseCoeff_three_eq_forward F hc
  have hB4 := exteriorInverseCoeff_four_eq_forward F hc
  have hB6 := exteriorInverseCoeff_six_eq_forward F hc
  have hB3 := exteriorInverseCoeff_three_norm_le_one F hc
  have hB5 := exteriorInverseCoeff_five_norm_le_one_add_firstCoeff_sq F hc
  have htail := exteriorForwardCoeff_finite_area_tail F hc 2 (by omega)
  norm_num [Finset.sum_Icc_succ_top] at htail
  have hB2sq : 2 * ‖exteriorInverseCoeff F 2‖ ^ 2 ≤ 1 - y := by
    simpa only [hB2] using htail
  have hcombo : ‖exteriorInverseCoeff F 3 +
      2 * (exteriorForwardCoeff F 1) ^ 2‖ ≤ 1 + 2 * y := by
    calc
      _ ≤ ‖exteriorInverseCoeff F 3‖ +
          ‖(2 : ℂ) * (exteriorForwardCoeff F 1) ^ 2‖ := norm_add_le _ _
      _ = ‖exteriorInverseCoeff F 3‖ + 2 * y := by simp [y, β, norm_mul, norm_pow]
      _ ≤ _ := by linarith
  have hcomboSq : ‖exteriorInverseCoeff F 3 +
      2 * (exteriorForwardCoeff F 1) ^ 2‖ ^ 2 ≤ (1 + 2 * y) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hcombo
  let weights1 : ℕ → ℂ := fun j =>
    if j = 2 then 7 * (exteriorInverseCoeff F 3 + 2 * (exteriorForwardCoeff F 1) ^ 2)
    else if j = 4 then 7 * exteriorForwardCoeff F 1 else if j = 6 then 1 else 0
  have hpair1 := exteriorForwardCoeff_weighted_linear_combination_sq_le
    F hc 6 (by omega) weights1
  norm_num [weights1, Finset.sum_Icc_succ_top, norm_mul] at hpair1
  have hfirstEq : exteriorInverseCoeff F 6 +
      2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 4 +
      2 * exteriorInverseCoeff F 2 * exteriorInverseCoeff F 3 +
      3 * (exteriorInverseCoeff F 1) ^ 2 * exteriorInverseCoeff F 2 =
      7 * (exteriorInverseCoeff F 3 + 2 * (exteriorForwardCoeff F 1) ^ 2) *
          exteriorForwardCoeff F 2 +
        7 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 + exteriorForwardCoeff F 6 := by
    rw [hB1, hB2, hB3eq, hB4, hB6]
    ring
  have hfirst : ‖exteriorInverseCoeff F 6 +
      2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 4 +
      2 * exteriorInverseCoeff F 2 * exteriorInverseCoeff F 3 +
      3 * (exteriorInverseCoeff F 1) ^ 2 * exteriorInverseCoeff F 2‖ ^ 2 ≤
      ((49 / 2 : ℝ) * (1 + 2 * y) ^ 2 + (49 / 4 : ℝ) * y + 1 / 6) * (1 - y) := by
    rw [hfirstEq]
    have hmult := mul_le_mul_of_nonneg_right
      (show (49 / 2 : ℝ) * ‖exteriorInverseCoeff F 3 +
          2 * (exteriorForwardCoeff F 1) ^ 2‖ ^ 2 + (49 / 4 : ℝ) * y + 1 / 6 ≤
        (49 / 2 : ℝ) * (1 + 2 * y) ^ 2 + (49 / 4 : ℝ) * y + 1 / 6 by linarith)
      (sub_nonneg.mpr hy1)
    apply hpair1.trans
    convert hmult using 1 <;> (try dsimp only [y, β]) <;> ring
  have hsecond : ‖2 * exteriorInverseCoeff F 5 +
      6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
      3 * (exteriorInverseCoeff F 2) ^ 2 + 4 * (exteriorInverseCoeff F 1) ^ 3‖ ≤
      (13 + 15 * y) / 2 := by
    have htri1 := norm_add_le
      (2 * exteriorInverseCoeff F 5 + 6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
        3 * (exteriorInverseCoeff F 2) ^ 2) (4 * (exteriorInverseCoeff F 1) ^ 3)
    have htri2 := norm_add_le
      (2 * exteriorInverseCoeff F 5 + 6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3)
      (3 * (exteriorInverseCoeff F 2) ^ 2)
    have htri3 := norm_add_le (2 * exteriorInverseCoeff F 5)
      (6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3)
    simp only [norm_mul, norm_pow, hB1, Complex.norm_ofNat] at htri1 htri2 htri3
    have hprod : 6 * β * ‖exteriorInverseCoeff F 3‖ ≤ 6 * β := by nlinarith
    rw [hB1]
    dsimp only [y, β] at hcube hβlin hB2sq hprod ⊢
    nlinarith
  have hsecondsq : ‖2 * exteriorInverseCoeff F 5 +
      6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
      3 * (exteriorInverseCoeff F 2) ^ 2 + 4 * (exteriorInverseCoeff F 1) ^ 3‖ ^ 2 ≤
      ((13 + 15 * y) / 2) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsecond
  let weights3 : ℕ → ℂ := fun j =>
    if j = 2 then 21 * exteriorForwardCoeff F 1 else if j = 4 then 3 else 0
  have hpair3 := exteriorForwardCoeff_weighted_linear_combination_sq_le
    F hc 4 (by omega) weights3
  norm_num [weights3, Finset.sum_Icc_succ_top, norm_mul] at hpair3
  have hthird : ‖3 * exteriorInverseCoeff F 4 +
      12 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2‖ ^ 2 ≤
      ((9 / 4 : ℝ) + (441 / 2 : ℝ) * y) * (1 - y) := by
    rw [hB1, hB2, hB4]
    convert hpair3 using 1 <;> (try dsimp only [y, β]) <;> ring
  have hfourth : ‖4 * exteriorInverseCoeff F 3 +
      10 * (exteriorInverseCoeff F 1) ^ 2‖ ≤ 4 + 10 * y := by
    calc
      _ ≤ ‖(4 : ℂ) * exteriorInverseCoeff F 3‖ +
          ‖(10 : ℂ) * (exteriorInverseCoeff F 1) ^ 2‖ := norm_add_le _ _
      _ = 4 * ‖exteriorInverseCoeff F 3‖ + 10 * y := by simp [hB1, y, β, norm_mul, norm_pow]
      _ ≤ _ := by linarith
  have hfourthsq : ‖4 * exteriorInverseCoeff F 3 +
      10 * (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 ≤ (4 + 10 * y) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hfourth
  have hscalar :
      ((49 / 2 : ℝ) * (1 + 2 * y) ^ 2 + (49 / 4 : ℝ) * y + 1 / 6) * (1 - y) +
        ((13 + 15 * y) / 2) ^ 2 +
        ((9 / 4 : ℝ) + (441 / 2 : ℝ) * y) * (1 - y) +
        (4 + 10 * y) ^ 2 + (25 / 2 : ℝ) * (1 - y) + 36 * y + 1 ≤
      (2227 + 347 * y) / 6 := by
    have hfactor : 0 ≤ (1 - y) ^ 2 * (196 * y + 545) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    nlinarith
  rw [schoberActualDiagonal_eight F hc]
  have hcombine : schoberActualDiagonal F 8 ≤
      ((49 / 2 : ℝ) * (1 + 2 * y) ^ 2 + (49 / 4 : ℝ) * y + 1 / 6) * (1 - y) +
        ((13 + 15 * y) / 2) ^ 2 +
        ((9 / 4 : ℝ) + (441 / 2 : ℝ) * y) * (1 - y) +
        (4 + 10 * y) ^ 2 + (25 / 2 : ℝ) * (1 - y) + 36 * y + 1 := by
    rw [schoberActualDiagonal_eight F hc, hB1]
    rw [hB1] at hfirst hsecondsq hthird hfourthsq
    dsimp only [y, β] at hB2sq hfirst hsecondsq hthird hfourthsq ⊢
    linarith
  simpa only [schoberActualDiagonal_eight F hc] using hcombine.trans hscalar

theorem schoberActualDiagonal_eight_lt_of_interior
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    schoberActualDiagonal F 8 < 429 := by
  have h := schoberActualDiagonal_eight_param_le F hc
  nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]

end SpringerLean
