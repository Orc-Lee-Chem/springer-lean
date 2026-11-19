import SpringerLean.Round120FiniteNormalize
import SpringerLean.Round119FiveMatrix

namespace SpringerLean

/-- Development bridge: once the independently read actual fifth Faber
modes are identified with the finite logarithmic kernel, the already proved
area estimate yields the normalized 5×5 contraction. The identification is
an explicit premise here and must be eliminated for a paper-level theorem. -/
theorem exterior_schoberKernelQ5_normalized_contraction_of_mode_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hmode : ∀ i j : Fin 5,
      fifthActualFaberMode F i j =
        ((i.val + 1 : ℕ) : ℂ) *
          schoberBiCoeff (j.val + 1) (i.val + 1)
            (schoberKernelQ5
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
              (exteriorForwardCoeff F 9)))
    (v : Fin 5 → ℂ) :
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
      ∑ i : Fin 5, ‖v i‖ ^ 2 := by
  let c : Fin 5 → Fin 5 → ℂ := fun j i =>
    schoberBiCoeff (j.val + 1) (i.val + 1)
      (schoberKernelQ5
        (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
        (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
        (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
        (exteriorForwardCoeff F 7) (exteriorForwardCoeff F 8)
        (exteriorForwardCoeff F 9))
  have hweighted (α : Fin 5 → ℂ) :
      (∑ j : Fin 5, ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 5, α i * ((i.val + 1 : ℕ) : ℂ) * c j i‖ ^ 2) ≤
        ∑ i : Fin 5, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2 := by
    have h := exterior_fifthActualFaberMode_weighted_contraction F hc α
    simpa only [c, hmode, mul_assoc] using h
  exact finiteDim_weighted_kernel_normalize 5 c hweighted v

end SpringerLean
