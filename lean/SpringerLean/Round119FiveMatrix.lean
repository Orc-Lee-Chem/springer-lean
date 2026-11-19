import SpringerLean.Round118FiveActualArea

set_option maxHeartbeats 1000000

namespace SpringerLean

/-- Five-by-five finite Faber-mode matrix read independently from actual
Taylor derivatives of the original exterior map's first five Faber factors.
For zero-based row `i` and column `j`, the Taylor degree is `i+j+2`. -/
noncomputable def fifthActualFaberMode
    (F : ℂ → ℂ) (i j : Fin 5) : ℂ :=
  if i = 0 then actualTaylorCoeff (exteriorPhi F) (j.val + 2)
  else if i = 1 then actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) (j.val + 3)
  else if i = 2 then actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) (j.val + 4)
  else if i = 3 then actualTaylorCoeff
    (fourthFaberFactor F) (j.val + 5)
  else actualTaylorCoeff (fifthFaberFactor F) (j.val + 6)

/-- A matrix column is the corresponding negative Fourier mode of the
genuine five-vector Faber boundary factor. -/
theorem fifthActualFaberMode_column_eq_actual
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 5 → ℂ) (j : Fin 5) :
    (∑ i : Fin 5, α i * fifthActualFaberMode F i j) =
      actualTaylorCoeff
        (fifthFaberCombinationFactor F
          (α 0) (α 1) (α 2) (α 3) (α 4))
        (j.val + 6) := by
  rw [Fin.sum_univ_five]
  have h := fifthFaberCombinationFactor_actual_coeff_decomp
    F hc (α 0) (α 1) (α 2) (α 3) (α 4) (j.val + 2)
  simpa [fifthActualFaberMode, Nat.add_assoc] using h.symm

/-- Actual all-vector weighted ℓ² contraction for the fifth Faber matrix.
The entries are genuine Taylor reads, with no Grunsky hypothesis. -/
theorem exterior_fifthActualFaberMode_weighted_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 5 → ℂ) :
    (∑ j : Fin 5,
      ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 5, α i * fifthActualFaberMode F i j‖ ^ 2) ≤
      ∑ i : Fin 5,
        ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  have h := exterior_fifthFaber_all_vector_energy_le
    F hc (α 0) (α 1) (α 2) (α 3) (α 4)
  dsimp only at h
  simp only [Fin.sum_univ_five,
    fifthActualFaberMode_column_eq_actual F hc α]
  norm_num at *
  exact h

end SpringerLean
