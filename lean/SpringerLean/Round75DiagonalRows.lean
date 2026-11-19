import SpringerLean.Round74FiniteSupport

namespace SpringerLean

/-- The diagonal coefficient of Schober's comparison kernel, expressed as a
finite sum because the actual reciprocal inverse has a simple zero. -/
noncomputable def schoberActualDiagonal (F : ℂ → ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n, ‖schoberActualA F n j‖ ^ 2

theorem schoberActualDiagonal_three
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 3 =
      ‖exteriorInverseCoeff F 1‖ ^ 2 + 1 := by
  rcases schoberActualA_row_three F hc with ⟨h1, h2, h3⟩
  norm_num [schoberActualDiagonal, Finset.sum_Icc_succ_top, h1, h2, h3]

theorem schoberActualDiagonal_four
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 4 =
      ‖exteriorInverseCoeff F 2‖ ^ 2 +
      4 * ‖exteriorInverseCoeff F 1‖ ^ 2 + 1 := by
  rcases schoberActualA_row_four F hc with ⟨h1, h2, h3, h4⟩
  norm_num [schoberActualDiagonal, Finset.sum_Icc_succ_top,
    h1, h2, h3, h4, norm_mul]
  ring

theorem schoberActualDiagonal_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 5 =
      ‖exteriorInverseCoeff F 3 + (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 +
      4 * ‖exteriorInverseCoeff F 2‖ ^ 2 +
      9 * ‖exteriorInverseCoeff F 1‖ ^ 2 + 1 := by
  rcases schoberActualA_row_five F hc with ⟨h1, h2, h3, h4, h5⟩
  norm_num [schoberActualDiagonal, Finset.sum_Icc_succ_top,
    h1, h2, h3, h4, h5, norm_mul]
  ring

theorem schoberActualDiagonal_six
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 6 =
      ‖exteriorInverseCoeff F 4 +
        2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2‖ ^ 2 +
      ‖2 * exteriorInverseCoeff F 3 +
        3 * (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 +
      9 * ‖exteriorInverseCoeff F 2‖ ^ 2 +
      16 * ‖exteriorInverseCoeff F 1‖ ^ 2 + 1 := by
  rcases schoberActualA_row_six F hc with ⟨h1, h2, h3, h4, h5, h6⟩
  norm_num [schoberActualDiagonal, Finset.sum_Icc_succ_top,
    h1, h2, h3, h4, h5, h6, norm_mul]
  ring

theorem schoberActualDiagonal_seven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 7 =
      ‖exteriorInverseCoeff F 5 +
          2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
          (exteriorInverseCoeff F 2) ^ 2 +
          (exteriorInverseCoeff F 1) ^ 3‖ ^ 2 +
      ‖2 * exteriorInverseCoeff F 4 +
          6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2‖ ^ 2 +
      ‖3 * exteriorInverseCoeff F 3 +
          6 * (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 +
      16 * ‖exteriorInverseCoeff F 2‖ ^ 2 +
      25 * ‖exteriorInverseCoeff F 1‖ ^ 2 + 1 := by
  rcases schoberActualA_row_seven F hc with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  norm_num [schoberActualDiagonal, Finset.sum_Icc_succ_top,
    h1, h2, h3, h4, h5, h6, h7, norm_mul]
  ring

theorem schoberActualDiagonal_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 8 =
      ‖exteriorInverseCoeff F 6 +
          2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 4 +
          2 * exteriorInverseCoeff F 2 * exteriorInverseCoeff F 3 +
          3 * (exteriorInverseCoeff F 1) ^ 2 * exteriorInverseCoeff F 2‖ ^ 2 +
      ‖2 * exteriorInverseCoeff F 5 +
          6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
          3 * (exteriorInverseCoeff F 2) ^ 2 +
          4 * (exteriorInverseCoeff F 1) ^ 3‖ ^ 2 +
      ‖3 * exteriorInverseCoeff F 4 +
          12 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2‖ ^ 2 +
      ‖4 * exteriorInverseCoeff F 3 +
          10 * (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 +
      25 * ‖exteriorInverseCoeff F 2‖ ^ 2 +
      36 * ‖exteriorInverseCoeff F 1‖ ^ 2 + 1 := by
  rcases schoberActualA_row_eight F hc with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  norm_num [schoberActualDiagonal, Finset.sum_Icc_succ_top,
    h1, h2, h3, h4, h5, h6, h7, h8, norm_mul]
  ring

end SpringerLean
