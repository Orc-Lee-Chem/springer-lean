import SpringerLean.Round132FiveKernelActualMatrix

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- The finite inverse functional on negative monomials for the fifth
comparison-kernel diagonal, using the project's `G=w-∑ B_j w⁻ʲ` sign. -/
noncomputable def schoberFifthL (B₁ B₂ B₃ : ℂ) (j : ℕ) : ℂ :=
  if j = 1 then B₃ + B₁ ^ 2
  else if j = 2 then 2 * B₂
  else if j = 3 then 3 * B₁
  else if j = 5 then 1
  else 0

/-- This finite functional reads the same actual inverse branch as the
project's independently defined fifth inverse coefficient row. -/
theorem schoberActualA_row_five_eq_L
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (j : Fin 5) :
    schoberActualA F 5 (j.val + 1) =
      schoberFifthL (exteriorInverseCoeff F 1)
        (exteriorInverseCoeff F 2) (exteriorInverseCoeff F 3)
        (j.val + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := schoberActualA_row_five F hc
  fin_cases j <;>
    simp [schoberFifthL, h1, h2, h3, h4, h5]

/-- The first tensor test vector's weighted energy, before 1/1!. -/
theorem schoberFifthL_linear_energy (B₁ B₂ B₃ : ℂ) :
    (∑ i : Fin 5,
      ‖schoberFifthL B₁ B₂ B₃ (i.val + 1)‖ ^ 2 /
        ((i.val + 1 : ℕ) : ℝ)) =
      ‖B₃ + B₁ ^ 2‖ ^ 2 + 2 * ‖B₂‖ ^ 2 +
        3 * ‖B₁‖ ^ 2 + 1 / 5 := by
  simp [Fin.sum_univ_five, schoberFifthL]
  ring

/-- The second tensor test vector's weighted energy, before 1/2!. -/
theorem schoberFifthL_quadratic_energy (B₁ B₂ B₃ : ℂ) :
    (∑ i : Fin 5, ∑ j : Fin 5,
      ‖schoberFifthL B₁ B₂ B₃ (i.val + j.val + 2)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ))) =
      4 * ‖B₂‖ ^ 2 + 9 * ‖B₁‖ ^ 2 + 5 / 6 := by
  simp [Fin.sum_univ_five, schoberFifthL]
  ring

/-- The third tensor test vector's weighted energy, before 1/3!. -/
theorem schoberFifthL_cubic_energy (B₁ B₂ B₃ : ℂ) :
    (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
      ‖schoberFifthL B₁ B₂ B₃
          (i.val + j.val + k.val + 3)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
          ((k.val + 1 : ℕ) : ℝ))) =
      9 * ‖B₁‖ ^ 2 + 7 / 4 := by
  simp [Fin.sum_univ_five, schoberFifthL]
  ring

/-- The fourth tensor test vector's weighted energy, before 1/4!. -/
theorem schoberFifthL_quartic_energy (B₁ B₂ B₃ : ℂ) :
    (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5, ∑ l : Fin 5,
      ‖schoberFifthL B₁ B₂ B₃
          (i.val + j.val + k.val + l.val + 4)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
          ((k.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ))) = 2 := by
  simp [Fin.sum_univ_five, schoberFifthL]
  norm_num

/-- The fifth tensor test vector's weighted energy, before 1/5!. -/
theorem schoberFifthL_quintic_energy (B₁ B₂ B₃ : ℂ) :
    (∑ i : Fin 5, ∑ j : Fin 5, ∑ k : Fin 5,
      ∑ l : Fin 5, ∑ m : Fin 5,
      ‖schoberFifthL B₁ B₂ B₃
          (i.val + j.val + k.val + l.val + m.val + 5)‖ ^ 2 /
        (((i.val + 1 : ℕ) : ℝ) * ((j.val + 1 : ℕ) : ℝ) *
          ((k.val + 1 : ℕ) : ℝ) * ((l.val + 1 : ℕ) : ℝ) *
          ((m.val + 1 : ℕ) : ℝ))) = 1 := by
  simp [Fin.sum_univ_five, schoberFifthL]

/-- The five factorial-weighted energies sum to the actual fifth
comparison-kernel diagonal polynomial. -/
theorem schoberFifthL_total_energy_arithmetic (B₁ B₂ B₃ : ℂ) :
    (‖B₃ + B₁ ^ 2‖ ^ 2 + 2 * ‖B₂‖ ^ 2 +
        3 * ‖B₁‖ ^ 2 + 1 / 5) +
      (1 / 2 : ℝ) * (4 * ‖B₂‖ ^ 2 + 9 * ‖B₁‖ ^ 2 + 5 / 6) +
      (1 / 6 : ℝ) * (9 * ‖B₁‖ ^ 2 + 7 / 4) +
      (1 / 24 : ℝ) * 2 + (1 / 120 : ℝ) =
      ‖B₃ + B₁ ^ 2‖ ^ 2 + 4 * ‖B₂‖ ^ 2 +
        9 * ‖B₁‖ ^ 2 + 1 := by
  ring

end SpringerLean
