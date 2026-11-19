import SpringerLean.Round97FaberScaling

namespace SpringerLean

/-- A finite matrix read independently from the actual Taylor coefficients
of the first four genuine Faber factors. Row `i` starts at Taylor degree
`i+j+2` for zero-based indices `i,j : Fin 4`. -/
noncomputable def fourthActualFaberMode
    (F : ℂ → ℂ) (i j : Fin 4) : ℂ :=
  if i = 0 then actualTaylorCoeff (exteriorPhi F) (j.val + 2)
  else if i = 1 then actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) (j.val + 3)
  else if i = 2 then actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) (j.val + 4)
  else actualTaylorCoeff (fourthFaberFactor F) (j.val + 5)

/-- Every column of the independently read finite matrix is the matching
negative Fourier mode of the actual four-vector Faber boundary factor. -/
theorem fourthActualFaberMode_column_eq_actual
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 4 → ℂ) (j : Fin 4) :
    (∑ i : Fin 4, α i * fourthActualFaberMode F i j) =
      actualTaylorCoeff
        (fourthFaberCombinationFactor F (α 0) (α 1) (α 2) (α 3))
        (j.val + 5) := by
  rw [Fin.sum_univ_four]
  have h := fourthFaberCombinationFactor_actual_coeff_decomp
    F hc (α 0) (α 1) (α 2) (α 3) (j.val + 2)
  simpa [fourthActualFaberMode, Nat.add_assoc] using h.symm

/-- The fully original-map four-by-four Faber-mode matrix is a contraction
between the finite weighted ℓ² spaces. The matrix entries here are actual
Taylor reads; identifying them with logarithmic-kernel coefficients is the
next separate theorem. -/
theorem exterior_fourthActualFaberMode_weighted_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α : Fin 4 → ℂ) :
    (∑ j : Fin 4,
      ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 4, α i * fourthActualFaberMode F i j‖ ^ 2) ≤
      ∑ i : Fin 4,
        ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
  have h := exterior_fourthFaber_all_vector_energy_le
    F hc (α 0) (α 1) (α 2) (α 3)
  dsimp only at h
  simp only [Fin.sum_univ_four,
    fourthActualFaberMode_column_eq_actual F hc α]
  norm_num at *
  exact h

end SpringerLean
