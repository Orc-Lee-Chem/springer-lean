import SpringerLean.Round174KernelSixSecondReverse

namespace SpringerLean

/-- The second negative mode of the actual sixth Faber factor agrees with
six times the reversed `(2,6)` log-kernel coefficient of the same F. -/
theorem sixthFaberFactor_actual_mode_eight_eq_logKernel6
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 8 =
      6 * schoberBiCoeff 2 6
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rw [sixthFaberFactor_actual_mode_eight F hc,
    schoberKernelQ6_coeff_two_six]

/-- Only the last four entries of the sixth Faber row remain as premises.
This is a development bridge, not an unconditional paper assertion. -/
theorem sixthActualFaberMode_eq_logKernel6_of_last_row_tail2
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (htail : ∀ j : Fin 6, 2 ≤ j.val →
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
  apply sixthActualFaberMode_eq_logKernel6_of_last_row_tail F hc
  intro j hj
  fin_cases j
  · contradiction
  · simpa [sixthActualFaberMode] using
      sixthFaberFactor_actual_mode_eight_eq_logKernel6 F hc
  · exact htail 2 (by decide)
  · exact htail 3 (by decide)
  · exact htail 4 (by decide)
  · exact htail 5 (by decide)

end SpringerLean
