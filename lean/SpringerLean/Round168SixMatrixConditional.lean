import SpringerLean.Round167KernelSixOldBlock
import SpringerLean.Round132FiveKernelActualMatrix

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem sixthActualFaberMode_old_block
    (F : ℂ → ℂ) (i j : Fin 5) :
    sixthActualFaberMode F (Fin.castSucc i) (Fin.castSucc j) =
      fifthActualFaberMode F i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The old block and first five entries of the new column are already
identified. This development lemma isolates the remaining sixth Faber row;
the row premise must be discharged before a paper-level contraction. -/
theorem sixthActualFaberMode_eq_logKernel6_of_last_row
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hrow : ∀ j : Fin 6,
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
  have hlow (i j : Fin 6) (hi : i.val < 5) (hj : j.val < 5) :
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
    let i5 : Fin 5 := ⟨i.val, hi⟩
    let j5 : Fin 5 := ⟨j.val, hj⟩
    have hi_cast : Fin.castSucc i5 = i := Fin.ext rfl
    have hj_cast : Fin.castSucc j5 = j := Fin.ext rfl
    rw [← hi_cast, ← hj_cast, sixthActualFaberMode_old_block,
      fifthActualFaberMode_eq_logKernel5 F hc i5 j5]
    rw [← schoberKernelQ6_low_block_eq_Q5
      (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
      (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
      (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
      (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
      (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
      (exteriorForwardCoeff F 11) j5 i5]
    simp only [Fin.val_castSucc]
  by_cases hi : i.val < 5
  · by_cases hj : j.val < 5
    · exact hlow i j hi hj
    · have hj5 : j = 5 := by ext; omega
      subst j
      fin_cases i
      · simpa using sixthActualFaberMode_first_row_eq_kernel F hc (5 : Fin 6)
      · simpa [sixthActualFaberMode] using
          secondFaberFactor_actual_mode_eight_eq_logKernel6 F hc
      · simpa [sixthActualFaberMode] using
          thirdFaberFactor_actual_mode_nine_eq_logKernel6 F hc
      · simpa [sixthActualFaberMode] using
          fourthFaberFactor_actual_mode_ten_eq_logKernel6 F hc
      · simpa [sixthActualFaberMode] using
          fifthFaberFactor_actual_mode_eleven_eq_logKernel6 F hc
      · norm_num at hi
  · have hi5 : i = 5 := by ext; omega
    subst i
    simpa using hrow j

/-- A conditional bridge from the original map's already proved six-vector
area estimate to the square-root-normalized finite log-kernel contraction.
The sixth-row premise is explicit and is not a theorem about arbitrary
centered exterior maps until that row has been identified. -/
theorem exterior_schoberKernelQ6_normalized_contraction_of_last_row
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hrow : ∀ j : Fin 6,
      sixthActualFaberMode F 5 j =
        6 * schoberBiCoeff (j.val + 1) 6
          (schoberKernelQ6
            (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
            (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
            (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
            (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
            (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
            (exteriorForwardCoeff F 11)))
    (v : Fin 6 → ℂ) :
    (∑ j : Fin 6,
      ‖∑ i : Fin 6,
        ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          schoberBiCoeff (j.val + 1) (i.val + 1)
            (schoberKernelQ6
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
              (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
              (exteriorForwardCoeff F 11)) * v i‖ ^ 2) ≤
      ∑ i : Fin 6, ‖v i‖ ^ 2 := by
  let c : Fin 6 → Fin 6 → ℂ := fun j i =>
    schoberBiCoeff (j.val + 1) (i.val + 1)
      (schoberKernelQ6
        (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
        (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
        (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
        (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
        (exteriorForwardCoeff F 9) (exteriorForwardCoeff F 10)
        (exteriorForwardCoeff F 11))
  have hmode := sixthActualFaberMode_eq_logKernel6_of_last_row F hc hrow
  have hweighted (α : Fin 6 → ℂ) :
      (∑ j : Fin 6, ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 6, α i * ((i.val + 1 : ℕ) : ℂ) * c j i‖ ^ 2) ≤
        ∑ i : Fin 6, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
    have h := exterior_sixthActualFaberMode_weighted_contraction F hc α
    simpa only [c, hmode, mul_assoc] using h
  exact finiteDim_weighted_kernel_normalize 6 c hweighted v

end SpringerLean
