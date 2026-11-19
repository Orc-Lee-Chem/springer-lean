import SpringerLean.Round128FiveFaberThirdMode

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- All 16 old entries of the fifth finite logarithmic kernel agree with
the previously verified fourth-order kernel. This is finite algebra and
does not assert the still-missing fifth inverse diagonal estimate. -/
theorem schoberKernelQ5_low_block_eq_Q4
    (b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉ : ℂ) (i j : Fin 4) :
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ5 b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉) =
    schoberBiCoeff (i.val + 1) (j.val + 1)
      (schoberKernelQ4 b₁ b₂ b₃ b₄ b₅ b₆ b₇) := by
  obtain ⟨h11, h21, h31, h41, h51⟩ :=
    schoberKernelQ5_first_row b₁ b₂ b₃ b₄ b₅ b₆ b₇ b₈ b₉
  obtain ⟨h'11, h'21, h'31⟩ :=
    schoberKernelQ4_first_row_low b₁ b₂ b₃ b₄ b₅ b₆ b₇
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two,
      Nat.zero_add, Nat.reduceAdd] <;>
    simp [h11, h21, h31, h41, h'11, h'21, h'31,
      schoberKernelQ4_coeff_four_one,
      schoberKernelQ5_coeff_one_two,
      schoberKernelQ5_coeff_two_two,
      schoberKernelQ5_coeff_three_two,
      schoberKernelQ5_coeff_four_two,
      schoberKernelQ5_coeff_one_three,
      schoberKernelQ5_coeff_two_three,
      schoberKernelQ5_coeff_three_three,
      schoberKernelQ5_coeff_four_three,
      schoberKernelQ5_coeff_one_four,
      schoberKernelQ5_coeff_two_four,
      schoberKernelQ5_coeff_three_four,
      schoberKernelQ5_coeff_four_four,
      schoberKernelQ4_coeff_one_two,
      schoberKernelQ4_coeff_two_two,
      schoberKernelQ4_coeff_three_two,
      schoberKernelQ4_coeff_four_two,
      schoberKernelQ4_coeff_one_three,
      schoberKernelQ4_coeff_two_three,
      schoberKernelQ4_coeff_three_three,
      schoberKernelQ4_coeff_four_three,
      schoberKernelQ4_coeff_one_four,
      schoberKernelQ4_coeff_two_four,
      schoberKernelQ4_coeff_three_four,
      schoberKernelQ4_coeff_four_four] <;>
    ring <;> simp

end SpringerLean
