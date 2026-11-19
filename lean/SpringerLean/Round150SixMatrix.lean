import SpringerLean.Round149SixActualArea

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- Actual six-by-six Faber-mode matrix of a single original exterior map.
Rows are independently read from genuine derivatives at zero; zero-based
entry `(i,j)` has Taylor degree `i+j+2` in the `(i+1)`st Faber factor. -/
noncomputable def sixthActualFaberMode
    (F : ℂ → ℂ) (i j : Fin 6) : ℂ :=
  if i = 0 then actualTaylorCoeff (exteriorPhi F) (j.val + 2)
  else if i = 1 then actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) (j.val + 3)
  else if i = 2 then actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) (j.val + 4)
  else if i = 3 then actualTaylorCoeff (fourthFaberFactor F) (j.val + 5)
  else if i = 4 then actualTaylorCoeff (fifthFaberFactor F) (j.val + 6)
  else actualTaylorCoeff (sixthFaberFactor F) (j.val + 7)

theorem sixthActualFaberMode_column_eq_actual
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 6 → ℂ) (j : Fin 6) :
    (∑ i : Fin 6, α i * sixthActualFaberMode F i j) =
      actualTaylorCoeff
        (sixthFaberCombinationFactor F
          (α 0) (α 1) (α 2) (α 3) (α 4) (α 5))
        (j.val + 7) := by
  rw [Fin.sum_univ_six]
  have h := sixthFaberCombinationFactor_actual_coeff_decomp
    F hc (α 0) (α 1) (α 2) (α 3) (α 4) (α 5) (j.val + 2)
  simpa [sixthActualFaberMode, Nat.add_assoc] using h.symm

/-- The actual sixth Faber-mode matrix is a weighted ℓ² contraction,
including every cross term between its six rows. -/
theorem exterior_sixthActualFaberMode_weighted_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 6 → ℂ) :
    (∑ j : Fin 6,
      ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 6, α i * sixthActualFaberMode F i j‖ ^ 2) ≤
      ∑ i : Fin 6,
        ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  have h := exterior_sixthFaber_all_vector_energy_le
    F hc (α 0) (α 1) (α 2) (α 3) (α 4) (α 5)
  dsimp only at h
  simp only [Fin.sum_univ_six,
    sixthActualFaberMode_column_eq_actual F hc α]
  norm_num at *
  exact h

end SpringerLean
