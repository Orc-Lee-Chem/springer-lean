import SpringerLean.Round121FiveKernelConditional

namespace SpringerLean

/-- The first row of the original-map fifth Faber matrix is the first row
of the independently checked fifth logarithmic kernel. -/
theorem fifthActualFaberMode_first_row_eq_kernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (j : Fin 5) :
    fifthActualFaberMode F 0 j =
      schoberBiCoeff (j.val + 1) 1
        (schoberKernelQ5
          (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
          (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
          (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
          (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
          (exteriorForwardCoeff F 9)) := by
  rcases schoberKernelQ5_first_row
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
      (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
      (exteriorForwardCoeff F 9) with
    ⟨h1, h2, h3, h4, h5⟩
  fin_cases j
  · simp only [fifthActualFaberMode, ↓reduceIte,
      Fin.val_zero, Nat.zero_add, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 1]
    exact h1.symm
  · simp only [fifthActualFaberMode, ↓reduceIte,
      Fin.val_one, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 2]
    exact h2.symm
  · simp only [fifthActualFaberMode, ↓reduceIte,
      Fin.val_two, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 3]
    exact h3.symm
  · simp only [fifthActualFaberMode, ↓reduceIte, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 4]
    exact h4.symm
  · simp only [fifthActualFaberMode, ↓reduceIte, Nat.reduceAdd]
    rw [actualTaylorCoeff_exteriorPhi_succ F hc 5]
    exact h5.symm

end SpringerLean
