import SpringerLean.Round129KernelFiveLowBlock
import SpringerLean.Round130FiveFaberFourthMode
import SpringerLean.Round131FiveFaberFifthMode

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem fifthActualFaberMode_old_block
    (F : ℂ → ℂ) (i j : Fin 4) :
    fifthActualFaberMode F (Fin.castSucc i) (Fin.castSucc j) =
      fourthActualFaberMode F i j := by
  fin_cases i <;> fin_cases j <;>
    rfl

/-- Every entry of the actual fifth Faber matrix equals the matching
fifth-order finite logarithmic-kernel coefficient of the same map. -/
theorem fifthActualFaberMode_eq_logKernel5
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (i j : Fin 5) :
    fifthActualFaberMode F i j =
      ((i.val + 1 : ℕ) : ℂ) *
        schoberBiCoeff (j.val + 1) (i.val + 1)
          (schoberKernelQ5
            (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
            (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
            (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
            (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
            (exteriorForwardCoeff F 9)) := by
  have hlow (i j : Fin 5) (hi : i.val < 4) (hj : j.val < 4) :
      fifthActualFaberMode F i j =
        ((i.val + 1 : ℕ) : ℂ) *
          schoberBiCoeff (j.val + 1) (i.val + 1)
            (schoberKernelQ5
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
              (exteriorForwardCoeff F 9)) := by
    let i4 : Fin 4 := ⟨i.val, hi⟩
    let j4 : Fin 4 := ⟨j.val, hj⟩
    have hi_cast : Fin.castSucc i4 = i := Fin.ext rfl
    have hj_cast : Fin.castSucc j4 = j := Fin.ext rfl
    rw [← hi_cast, ← hj_cast,
      fifthActualFaberMode_old_block,
      fourthActualFaberMode_eq_logKernel4 F hc i4 j4]
    rw [← schoberKernelQ5_low_block_eq_Q4
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
      (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
      (exteriorForwardCoeff F 9) j4 i4]
    simp only [Fin.val_castSucc]
  by_cases hi : i.val < 4
  · by_cases hj : j.val < 4
    · exact hlow i j hi hj
    · have hj4 : j = 4 := by
        ext
        omega
      subst j
      fin_cases i
      · simpa using fifthActualFaberMode_first_row_eq_kernel F hc (4 : Fin 5)
      · simpa [fifthActualFaberMode] using
          secondFaberFactor_actual_mode_seven_eq_logKernel5 F hc
      · simpa [fifthActualFaberMode] using
          thirdFaberFactor_actual_mode_eight_eq_logKernel5 F hc
      · simpa [fifthActualFaberMode] using
          fourthFaberFactor_actual_mode_nine_eq_logKernel5 F hc
      · norm_num at hi
  · have hi4 : i = 4 := by
      ext
      omega
    subst i
    fin_cases j
    · simpa [fifthActualFaberMode] using
        fifthFaberFactor_actual_mode_six_eq_logKernel5 F hc
    · simpa [fifthActualFaberMode] using
        fifthFaberFactor_actual_mode_seven_eq_logKernel5 F hc
    · simpa [fifthActualFaberMode] using
        fifthFaberFactor_actual_mode_eight_eq_logKernel5 F hc
    · simpa [fifthActualFaberMode] using
        fifthFaberFactor_actual_mode_nine_eq_logKernel5 F hc
    · simpa [fifthActualFaberMode] using
        fifthFaberFactor_actual_mode_ten_eq_logKernel5 F hc

/-- Unconditional normalized five-by-five Grunsky contraction for every
original centered exterior-univalent map. -/
theorem exterior_schoberKernelQ5_normalized_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (v : Fin 5 → ℂ) :
    (∑ j : Fin 5,
      ‖∑ i : Fin 5,
        ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          schoberBiCoeff (j.val + 1) (i.val + 1)
            (schoberKernelQ5
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
              (exteriorForwardCoeff F 9)) * v i‖ ^ 2) ≤
      ∑ i : Fin 5, ‖v i‖ ^ 2 :=
  exterior_schoberKernelQ5_normalized_contraction_of_mode_eq
    F hc (fifthActualFaberMode_eq_logKernel5 F hc) v

end SpringerLean
