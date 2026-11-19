import SpringerLean.Round170KernelSixInnerLinear

namespace SpringerLean

/-- The first mode of the actual sixth Faber factor equals the reversed
first coefficient of the finite logarithmic kernel for the same map. -/
theorem sixthFaberFactor_actual_mode_seven_eq_logKernel6
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (sixthFaberFactor F) 7 =
      6 * schoberBiCoeff 1 6
        (schoberKernelQ6
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
          (exteriorForwardCoeff F 11)) := by
  rw [sixthFaberFactor_actual_mode_seven F hc,
    schoberKernelQ6_coeff_one_six]

/-- Only the remaining five entries of the sixth Faber row are premises.
All other entries of the actual six-dimensional matrix have already been
identified unconditionally. -/
theorem sixthActualFaberMode_eq_logKernel6_of_last_row_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (htail : ∀ j : Fin 6, j ≠ 0 →
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
  apply sixthActualFaberMode_eq_logKernel6_of_last_row F hc
  · intro j
    by_cases hj : j = 0
    · subst j
      simpa [sixthActualFaberMode] using
        sixthFaberFactor_actual_mode_seven_eq_logKernel6 F hc
    · exact htail j hj

end SpringerLean
