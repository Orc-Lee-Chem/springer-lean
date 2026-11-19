import SpringerLean.Round177SixFaberThirdMode
import SpringerLean.Round181KernelSixThirdReverse

namespace SpringerLean

/-- Third negative mode of the actual sixth Faber factor, matched to the
reversed `(3,6)` coefficient of the finite logarithmic kernel. -/
theorem sixthFaberFactor_actual_mode_nine_eq_logKernel6
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 9 =
      6 * schoberBiCoeff 3 6
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rw [sixthFaberFactor_actual_mode_nine F hc,
    schoberKernelQ6_coeff_three_six]

/-- The actual matrix is now identified apart from the last three entries
of its sixth Faber row. This explicit-premise lemma is for development. -/
theorem sixthActualFaberMode_eq_logKernel6_of_last_row_tail3
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (htail : ∀ j : Fin 6, 3 ≤ j.val →
      sixthActualFaberMode F 5 j =
        6 * schoberBiCoeff (j.val + 1) 6
          (schoberKernelQ6
            (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
            (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
            (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
            (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
            (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
            (exteriorForwardCoeff F 11)))
    (i j : Fin 6) :
    sixthActualFaberMode F i j =
      ((i.val + 1 : ℕ) : ℂ) *
        schoberBiCoeff (j.val + 1) (i.val + 1)
          (schoberKernelQ6
            (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
            (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
            (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
            (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
            (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
            (exteriorForwardCoeff F 11)) := by
  apply sixthActualFaberMode_eq_logKernel6_of_last_row_tail2 F hc
  intro j hj
  fin_cases j
  · contradiction
  · norm_num at hj
  · simpa [sixthActualFaberMode] using
      sixthFaberFactor_actual_mode_nine_eq_logKernel6 F hc
  · exact htail 3 (by decide)
  · exact htail 4 (by decide)
  · exact htail 5 (by decide)

end SpringerLean
