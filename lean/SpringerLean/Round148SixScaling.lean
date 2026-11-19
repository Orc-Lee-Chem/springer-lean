import SpringerLean.Round147SixLowCombination
import SpringerLean.Round117FiveScaling

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem round148_rescale_C (s a : ℂ) :
    PowerSeries.rescale s (PowerSeries.C a) = PowerSeries.C a := by
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_rescale]
  by_cases hj : j = 0
  · subst j
    simp
  · simp [PowerSeries.coeff_C, hj]

/-- The sixth actual Faber factor scales in the same Taylor variable as
the first five factors. -/
theorem sixthFaberFactor_actualTaylorSeries_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    actualTaylorSeries (sixthFaberFactor (rescaleExterior s F)) =
      PowerSeries.rescale (s : ℂ)
        (actualTaylorSeries (sixthFaberFactor F)) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [sixthFaberFactor_actualTaylorSeries _ hcG,
    sixthFaberFactor_actualTaylorSeries F hc]
  simp only [sixthFaberFormalFactor,
    formalExteriorPhi_rescale_exterior F hc hs0,
    rescaleExterior_forwardCoeff F hc hs0,
    map_add, map_sub, map_pow, map_mul,
    PowerSeries.rescale_X, round148_rescale_C]
  ring

theorem sixthFaberFactor_actualCoeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    actualTaylorCoeff (sixthFaberFactor (rescaleExterior s F)) j =
      (s : ℂ) ^ j * actualTaylorCoeff (sixthFaberFactor F) j := by
  have h := congrArg (PowerSeries.coeff j)
    (sixthFaberFactor_actualTaylorSeries_rescale F hc hs0 hs1)
  simpa only [actualTaylorSeries_coeff,
    PowerSeries.coeff_rescale] using h

/-- One common sixth-Faber mode is the sum of six actual Taylor reads,
one from each Faber row of the same map. -/
theorem sixthFaberCombinationFactor_actual_coeff_decomp
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (sixthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅ α₆) (k + 5) =
      α₁ * actualTaylorCoeff (exteriorPhi G) k +
      α₂ * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi G u ^ 2 - 2 * exteriorForwardCoeff G 1 * u ^ 2) (k + 1) +
      α₃ * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi G u ^ 3 -
          3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
          3 * exteriorForwardCoeff G 2 * u ^ 3) (k + 2) +
      α₄ * actualTaylorCoeff (fourthFaberFactor G) (k + 3) +
      α₅ * actualTaylorCoeff (fifthFaberFactor G) (k + 4) +
      α₆ * actualTaylorCoeff (sixthFaberFactor G) (k + 5) := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hfive : AnalyticAt ℂ
      (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) 0 := by
    unfold fifthFaberCombinationFactor fourthFaberCombinationFactor
      thirdFaberCombinationFactor fifthFaberFactor fourthFaberFactor
    fun_prop
  rw [sixthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅ α₆,
    show k + 5 = (k + 4) + 1 by omega,
    actualTaylorCoeff_var_mul_succ _ hfive (k + 4),
    fifthFaberCombinationFactor_actual_coeff_decomp
      G hc α₁ α₂ α₃ α₄ α₅ k]

/-- Explicit coefficientwise scaling preserves the six distinct powers
of `s` attached to the six Faber rows. -/
noncomputable def sixthFaberModeAtScale
    (F : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) (k : ℕ) (s : ℝ) : ℂ :=
  α₁ * (s : ℂ) ^ k * actualTaylorCoeff (exteriorPhi F) k +
  α₂ * (s : ℂ) ^ (k + 1) * actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) (k + 1) +
  α₃ * (s : ℂ) ^ (k + 2) * actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) (k + 2) +
  α₄ * (s : ℂ) ^ (k + 3) *
    actualTaylorCoeff (fourthFaberFactor F) (k + 3) +
  α₅ * (s : ℂ) ^ (k + 4) *
    actualTaylorCoeff (fifthFaberFactor F) (k + 4) +
  α₆ * (s : ℂ) ^ (k + 5) *
    actualTaylorCoeff (sixthFaberFactor F) (k + 5)

theorem sixthFaberModeAtScale_eq_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) (k : ℕ) :
    sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ k s =
      actualTaylorCoeff
        (sixthFaberCombinationFactor (rescaleExterior s F)
          α₁ α₂ α₃ α₄ α₅ α₆) (k + 5) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [sixthFaberCombinationFactor_actual_coeff_decomp
    (rescaleExterior s F) hcG α₁ α₂ α₃ α₄ α₅ α₆ k,
    exteriorPhi_actualCoeff_rescale F hc hs0 hs1 k,
    secondFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 1),
    thirdFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 2),
    fourthFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 3),
    fifthFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 4),
    sixthFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 5)]
  dsimp only [sixthFaberModeAtScale]
  ring

theorem sixthFaberModeAtScale_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ α₄ α₅ α₆ : ℂ) (k : ℕ) :
    sixthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ α₆ k 1 =
      actualTaylorCoeff
        (sixthFaberCombinationFactor F α₁ α₂ α₃ α₄ α₅ α₆) (k + 5) := by
  rw [sixthFaberCombinationFactor_actual_coeff_decomp
    F hc α₁ α₂ α₃ α₄ α₅ α₆ k]
  simp [sixthFaberModeAtScale]

end SpringerLean
