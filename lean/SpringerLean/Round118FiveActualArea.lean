import SpringerLean.Round117FiveScaling

namespace SpringerLean

/-- The fifth-order Green-area inequality for an arbitrary five-vector of
Faber polynomials of the original actual exterior map. Regularization and
its boundary hypotheses have disappeared from this statement. -/
theorem exterior_fifthFaber_all_vector_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) :
    let A := fifthFaberCombinationFactor F α₁ α₂ α₃ α₄ α₅
    ‖actualTaylorCoeff A 6‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 10‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 +
        5 * ‖α₅‖ ^ 2 := by
  let E : ℝ → ℝ := fun s =>
    ‖fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ 2 s‖ ^ 2 +
      2 * ‖fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ 3 s‖ ^ 2 +
      3 * ‖fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ 4 s‖ ^ 2 +
      4 * ‖fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ 5 s‖ ^ 2 +
      5 * ‖fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ 6 s‖ ^ 2
  have hcont : Continuous E := by
    dsimp only [E, fifthFaberModeAtScale]
    fun_prop
  have hlim : Filter.Tendsto
      (fun n : ℕ => E (omittedScaleSeq n)) Filter.atTop (nhds (E 1)) :=
    hcont.continuousAt.tendsto.comp omittedScaleSeq_tendsto_one
  have hbound (n : ℕ) : E (omittedScaleSeq n) ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 + 5 * ‖α₅‖ ^ 2 := by
    have h := rescaleExterior_fifthFaber_all_vector_energy_le
      F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
      α₁ α₂ α₃ α₄ α₅
    change ‖actualTaylorCoeff
        (fifthFaberCombinationFactor
          (rescaleExterior (omittedScaleSeq n) F)
          α₁ α₂ α₃ α₄ α₅) 6‖ ^ 2 +
      2 * ‖actualTaylorCoeff
          (fifthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅) 7‖ ^ 2 +
      3 * ‖actualTaylorCoeff
          (fifthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅) 8‖ ^ 2 +
      4 * ‖actualTaylorCoeff
          (fifthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅) 9‖ ^ 2 +
      5 * ‖actualTaylorCoeff
          (fifthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅) 10‖ ^ 2 ≤ _ at h
    rw [← fifthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ 2,
      ← fifthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ 3,
      ← fifthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ 4,
      ← fifthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ 5,
      ← fifthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ 6] at h
    exact h
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  dsimp only [E] at h
  rw [fifthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ 2,
    fifthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ 3,
    fifthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ 4,
    fifthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ 5,
    fifthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ 6] at h
  exact h

end SpringerLean
