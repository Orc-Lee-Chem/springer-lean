import SpringerLean.Round148SixScaling

namespace SpringerLean

/-- Arbitrary six-vector Faber area inequality for the original actual
exterior map. The regularization parameter and its boundary assumptions
have been removed by a finite-coefficient limit. -/
theorem exterior_sixthFaber_all_vector_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) :
    let A := sixthFaberCombinationFactor F α₁ α₂ α₃ α₄ α₅ α₆
    ‖actualTaylorCoeff A 7‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 8‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 9‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 10‖ ^ 2 +
        5 * ‖actualTaylorCoeff A 11‖ ^ 2 +
        6 * ‖actualTaylorCoeff A 12‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 +
        5 * ‖α₅‖ ^ 2 + 6 * ‖α₆‖ ^ 2 := by
  let E : ℝ → ℝ := fun s =>
    ‖sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ 2 s‖ ^ 2 +
      2 * ‖sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ 3 s‖ ^ 2 +
      3 * ‖sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ 4 s‖ ^ 2 +
      4 * ‖sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ 5 s‖ ^ 2 +
      5 * ‖sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ 6 s‖ ^ 2 +
      6 * ‖sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ 7 s‖ ^ 2
  have hcont : Continuous E := by
    dsimp only [E, sixthFaberModeAtScale]
    fun_prop
  have hlim : Filter.Tendsto
      (fun n : ℕ => E (omittedScaleSeq n)) Filter.atTop (nhds (E 1)) :=
    hcont.continuousAt.tendsto.comp omittedScaleSeq_tendsto_one
  have hbound (n : ℕ) : E (omittedScaleSeq n) ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 +
        5 * ‖α₅‖ ^ 2 + 6 * ‖α₆‖ ^ 2 := by
    have h := rescaleExterior_sixthFaber_all_vector_energy_le
      F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
      α₁ α₂ α₃ α₄ α₅ α₆
    change ‖actualTaylorCoeff
        (sixthFaberCombinationFactor
          (rescaleExterior (omittedScaleSeq n) F)
          α₁ α₂ α₃ α₄ α₅ α₆) 7‖ ^ 2 +
      2 * ‖actualTaylorCoeff
          (sixthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅ α₆) 8‖ ^ 2 +
      3 * ‖actualTaylorCoeff
          (sixthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅ α₆) 9‖ ^ 2 +
      4 * ‖actualTaylorCoeff
          (sixthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅ α₆) 10‖ ^ 2 +
      5 * ‖actualTaylorCoeff
          (sixthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅ α₆) 11‖ ^ 2 +
      6 * ‖actualTaylorCoeff
          (sixthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F)
            α₁ α₂ α₃ α₄ α₅ α₆) 12‖ ^ 2 ≤ _ at h
    rw [← sixthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ α₆ 2,
      ← sixthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ α₆ 3,
      ← sixthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ α₆ 4,
      ← sixthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ α₆ 5,
      ← sixthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ α₆ 6,
      ← sixthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ α₅ α₆ 7] at h
    exact h
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  dsimp only [E] at h
  rw [sixthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ α₆ 2,
    sixthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ α₆ 3,
    sixthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ α₆ 4,
    sixthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ α₆ 5,
    sixthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ α₆ 6,
    sixthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ α₅ α₆ 7] at h
  exact h

end SpringerLean
