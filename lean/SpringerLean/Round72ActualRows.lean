import SpringerLean.Round71PowerRows

namespace SpringerLean

noncomputable def schoberActualA (F : ℂ → ℂ) (n j : ℕ) : ℂ :=
  schoberA (schoberActualInverseSeries F) n j

/-- The coefficient `a(n,j)` is read from the analytic extension of the
actual inverse branch of the very same function `F`. -/
theorem schoberActualA_eq_actualTaylorCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n j : ℕ) :
    schoberActualA F n j =
      actualTaylorCoeff (fun t => (schoberActualReciprocalGerm F t) ^ j) n := by
  exact schoberActualPowerCoeff_eq_actualTaylorCoeff F hc n j

theorem schoberActualA_row_four
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualA F 4 1 = exteriorInverseCoeff F 2 ∧
    schoberActualA F 4 2 = 2 * exteriorInverseCoeff F 1 ∧
    schoberActualA F 4 3 = 0 ∧
    schoberActualA F 4 4 = 1 := by
  simpa [schoberActualA, schoberActualInverseSeries,
    actualTaylorCoeff_inverse] using
    schoberA_row_four (schoberActualInverseSeries F)
      (schoberActualInverseSeries_coeff_zero F)


theorem schoberActualA_row_three
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualA F 3 1 = exteriorInverseCoeff F 1 ∧
    schoberActualA F 3 2 = 0 ∧
    schoberActualA F 3 3 = 1 := by
  have h := schoberFiniteL_values (schoberActualInverseSeries F)
    (schoberActualInverseSeries_coeff_zero F)
  simpa [schoberActualA, schoberA, schoberFiniteL,
    schoberActualInverseSeries_coeff_one] using
    (show schoberFiniteL (schoberActualInverseSeries F) 1 =
          PowerSeries.coeff 1 (schoberActualInverseSeries F) ∧
        schoberFiniteL (schoberActualInverseSeries F) 2 = 0 ∧
        schoberFiniteL (schoberActualInverseSeries F) 3 = 1 from
      ⟨h.1, h.2.1, h.2.2.1⟩)

theorem schoberActualA_row_five
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualA F 5 1 = exteriorInverseCoeff F 3 +
        (exteriorInverseCoeff F 1) ^ 2 ∧
    schoberActualA F 5 2 = 2 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 5 3 = 3 * exteriorInverseCoeff F 1 ∧
    schoberActualA F 5 4 = 0 ∧
    schoberActualA F 5 5 = 1 := by
  simpa [schoberActualA, schoberActualInverseSeries,
    actualTaylorCoeff_inverse] using
    schoberA_row_five (schoberActualInverseSeries F)
      (schoberActualInverseSeries_coeff_zero F)

theorem schoberActualA_row_six
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualA F 6 1 = exteriorInverseCoeff F 4 +
        2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 6 2 = 2 * exteriorInverseCoeff F 3 +
        3 * (exteriorInverseCoeff F 1) ^ 2 ∧
    schoberActualA F 6 3 = 3 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 6 4 = 4 * exteriorInverseCoeff F 1 ∧
    schoberActualA F 6 5 = 0 ∧
    schoberActualA F 6 6 = 1 := by
  simpa [schoberActualA, schoberActualInverseSeries,
    actualTaylorCoeff_inverse] using
    schoberA_row_six (schoberActualInverseSeries F)
      (schoberActualInverseSeries_coeff_zero F)

theorem schoberActualA_row_seven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualA F 7 1 = exteriorInverseCoeff F 5 +
        2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
        (exteriorInverseCoeff F 2) ^ 2 + (exteriorInverseCoeff F 1) ^ 3 ∧
    schoberActualA F 7 2 = 2 * exteriorInverseCoeff F 4 +
        6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 7 3 = 3 * exteriorInverseCoeff F 3 +
        6 * (exteriorInverseCoeff F 1) ^ 2 ∧
    schoberActualA F 7 4 = 4 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 7 5 = 5 * exteriorInverseCoeff F 1 ∧
    schoberActualA F 7 6 = 0 ∧
    schoberActualA F 7 7 = 1 := by
  simpa [schoberActualA, schoberActualInverseSeries,
    actualTaylorCoeff_inverse] using
    schoberA_row_seven (schoberActualInverseSeries F)
      (schoberActualInverseSeries_coeff_zero F)

theorem schoberActualA_row_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualA F 8 1 = exteriorInverseCoeff F 6 +
        2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 4 +
        2 * exteriorInverseCoeff F 2 * exteriorInverseCoeff F 3 +
        3 * (exteriorInverseCoeff F 1) ^ 2 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 8 2 = 2 * exteriorInverseCoeff F 5 +
        6 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 3 +
        3 * (exteriorInverseCoeff F 2) ^ 2 +
        4 * (exteriorInverseCoeff F 1) ^ 3 ∧
    schoberActualA F 8 3 = 3 * exteriorInverseCoeff F 4 +
        12 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 8 4 = 4 * exteriorInverseCoeff F 3 +
        10 * (exteriorInverseCoeff F 1) ^ 2 ∧
    schoberActualA F 8 5 = 5 * exteriorInverseCoeff F 2 ∧
    schoberActualA F 8 6 = 6 * exteriorInverseCoeff F 1 ∧
    schoberActualA F 8 7 = 0 ∧
    schoberActualA F 8 8 = 1 := by
  simpa [schoberActualA, schoberActualInverseSeries,
    actualTaylorCoeff_inverse] using
    schoberA_row_eight (schoberActualInverseSeries F)
      (schoberActualInverseSeries_coeff_zero F)
end SpringerLean