import SpringerLean.Round116FiveLowModes

set_option maxHeartbeats 1000000

namespace SpringerLean

private theorem round117_rescale_C (s a : ℂ) :
    PowerSeries.rescale s (PowerSeries.C a) = PowerSeries.C a := by
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_rescale]
  by_cases hj : j = 0
  · subst j
    simp
  · simp [PowerSeries.coeff_C, hj]

/-- The fifth actual Faber factor scales coefficientwise, with no extra
boundary hypothesis on the original exterior map. -/
theorem fifthFaberFactor_actualTaylorSeries_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    actualTaylorSeries (fifthFaberFactor (rescaleExterior s F)) =
      PowerSeries.rescale (s : ℂ)
        (actualTaylorSeries (fifthFaberFactor F)) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [fifthFaberFactor_actualTaylorSeries _ hcG,
    fifthFaberFactor_actualTaylorSeries F hc]
  simp only [fifthFaberFormalFactor,
    formalExteriorPhi_rescale_exterior F hc hs0,
    rescaleExterior_forwardCoeff F hc hs0,
    map_add, map_sub, map_pow, map_mul,
    PowerSeries.rescale_X, round117_rescale_C]
  ring

theorem fifthFaberFactor_actualCoeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    actualTaylorCoeff (fifthFaberFactor (rescaleExterior s F)) j =
      (s : ℂ) ^ j * actualTaylorCoeff (fifthFaberFactor F) j := by
  have h := congrArg (PowerSeries.coeff j)
    (fifthFaberFactor_actualTaylorSeries_rescale F hc hs0 hs1)
  simpa only [actualTaylorSeries_coeff,
    PowerSeries.coeff_rescale] using h

/-- The common frequency-five factor decomposes into the five actual
Faber rows at every negative Fourier mode. -/
theorem fifthFaberCombinationFactor_actual_coeff_decomp
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (fifthFaberCombinationFactor G α₁ α₂ α₃ α₄ α₅) (k + 4) =
      α₁ * actualTaylorCoeff (exteriorPhi G) k +
      α₂ * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi G u ^ 2 - 2 * exteriorForwardCoeff G 1 * u ^ 2) (k + 1) +
      α₃ * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi G u ^ 3 -
          3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
          3 * exteriorForwardCoeff G 2 * u ^ 3) (k + 2) +
      α₄ * actualTaylorCoeff (fourthFaberFactor G) (k + 3) +
      α₅ * actualTaylorCoeff (fifthFaberFactor G) (k + 4) := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have hthree : AnalyticAt ℂ
      (thirdFaberCombinationFactor G α₁ α₂ α₃) 0 := by
    unfold thirdFaberCombinationFactor
    fun_prop
  have hfourthFactor : AnalyticAt ℂ (fourthFaberFactor G) 0 := by
    unfold fourthFaberFactor
    fun_prop
  have hfour : AnalyticAt ℂ
      (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) 0 := by
    change AnalyticAt ℂ (fun u : ℂ =>
      u * thirdFaberCombinationFactor G α₁ α₂ α₃ u +
        α₄ * fourthFaberFactor G u) 0
    exact (analyticAt_id.mul hthree).add
      (analyticAt_const.mul hfourthFactor)
  rw [fifthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄ α₅,
    show k + 4 = (k + 3) + 1 by omega,
    actualTaylorCoeff_var_mul_succ _ hfour (k + 3),
    fourthFaberCombinationFactor_actual_coeff_decomp
      G hc α₁ α₂ α₃ α₄ k]

/-- Explicit regularized fifth-combination mode, retaining the distinct
powers of `s` attached to each Faber row. -/
noncomputable def fifthFaberModeAtScale
    (F : ℂ → ℂ) (α₁ α₂ α₃ α₄ α₅ : ℂ) (k : ℕ) (s : ℝ) : ℂ :=
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
    actualTaylorCoeff (fifthFaberFactor F) (k + 4)

theorem fifthFaberModeAtScale_eq_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) (k : ℕ) :
    fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ k s =
      actualTaylorCoeff
        (fifthFaberCombinationFactor (rescaleExterior s F)
          α₁ α₂ α₃ α₄ α₅) (k + 4) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [fifthFaberCombinationFactor_actual_coeff_decomp
    (rescaleExterior s F) hcG α₁ α₂ α₃ α₄ α₅ k,
    exteriorPhi_actualCoeff_rescale F hc hs0 hs1 k,
    secondFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 1),
    thirdFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 2),
    fourthFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 3),
    fifthFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 4)]
  dsimp only [fifthFaberModeAtScale]
  ring

theorem fifthFaberModeAtScale_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ α₄ α₅ : ℂ) (k : ℕ) :
    fifthFaberModeAtScale F α₁ α₂ α₃ α₄ α₅ k 1 =
      actualTaylorCoeff
        (fifthFaberCombinationFactor F α₁ α₂ α₃ α₄ α₅) (k + 4) := by
  rw [fifthFaberCombinationFactor_actual_coeff_decomp
    F hc α₁ α₂ α₃ α₄ α₅ k]
  simp [fifthFaberModeAtScale]

end SpringerLean
