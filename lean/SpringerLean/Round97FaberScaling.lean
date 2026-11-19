import SpringerLean.Round96FourCombination

namespace SpringerLean

private theorem round97_rescale_C (s a : ℂ) :
    PowerSeries.rescale s (PowerSeries.C a) = PowerSeries.C a := by
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_rescale]
  by_cases hj : j = 0
  · subst j
    simp
  · simp [PowerSeries.coeff_C, hj]

/-- The first reciprocal Faber factor of a regularized actual map is the
rescaled Taylor series of the original map's factor. -/
theorem exteriorPhi_actualTaylorSeries_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    actualTaylorSeries (exteriorPhi (rescaleExterior s F)) =
      PowerSeries.rescale (s : ℂ)
        (actualTaylorSeries (exteriorPhi F)) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [exteriorPhi_actualTaylorSeries _ hcG,
    exteriorPhi_actualTaylorSeries F hc]
  exact formalExteriorPhi_rescale_exterior F hc hs0

/-- The second reciprocal Faber factor has the same exact all-order
rescaling law. -/
theorem secondFaberFactor_actualTaylorSeries_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    actualTaylorSeries (fun u : ℂ =>
      exteriorPhi (rescaleExterior s F) u ^ 2 -
        2 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2) =
      PowerSeries.rescale (s : ℂ)
        (actualTaylorSeries (fun u : ℂ =>
          exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2)) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [secondFaberFactor_actualTaylorSeries _ hcG,
    secondFaberFactor_actualTaylorSeries F hc]
  simp only [formalExteriorPhi_rescale_exterior F hc hs0,
    rescaleExterior_forwardCoeff F hc hs0,
    map_sub, map_pow, map_mul,
    PowerSeries.rescale_X, round97_rescale_C]
  ring

/-- The third reciprocal Faber factor likewise scales coefficientwise. -/
theorem thirdFaberFactor_actualTaylorSeries_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    actualTaylorSeries (fun u : ℂ =>
      exteriorPhi (rescaleExterior s F) u ^ 3 -
        3 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2 *
          exteriorPhi (rescaleExterior s F) u -
        3 * exteriorForwardCoeff (rescaleExterior s F) 2 * u ^ 3) =
      PowerSeries.rescale (s : ℂ)
        (actualTaylorSeries (fun u : ℂ =>
          exteriorPhi F u ^ 3 -
            3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
            3 * exteriorForwardCoeff F 2 * u ^ 3)) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [thirdFaberFactor_actualTaylorSeries _ hcG,
    thirdFaberFactor_actualTaylorSeries F hc]
  simp only [formalExteriorPhi_rescale_exterior F hc hs0,
    rescaleExterior_forwardCoeff F hc hs0,
    map_sub, map_pow, map_mul,
    PowerSeries.rescale_X, round97_rescale_C]
  ring

/-- A fourth-combination negative mode is the finite sum of four actual
Faber-factor Taylor reads. The index `k+3` avoids natural subtraction. -/
theorem fourthFaberCombinationFactor_actual_coeff_decomp
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (α₁ α₂ α₃ α₄ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (fourthFaberCombinationFactor G α₁ α₂ α₃ α₄) (k + 3) =
      α₁ * actualTaylorCoeff (exteriorPhi G) k +
      α₂ * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi G u ^ 2 - 2 * exteriorForwardCoeff G 1 * u ^ 2) (k + 1) +
      α₃ * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi G u ^ 3 -
          3 * exteriorForwardCoeff G 1 * u ^ 2 * exteriorPhi G u -
          3 * exteriorForwardCoeff G 2 * u ^ 3) (k + 2) +
      α₄ * actualTaylorCoeff (fourthFaberFactor G) (k + 3) := by
  have hφ : AnalyticAt ℂ (exteriorPhi G) 0 :=
    exteriorPhi_analyticAt G hc.2.2
  have h₂ : AnalyticAt ℂ (fun u : ℂ =>
      exteriorPhi G u ^ 2 - 2 * exteriorForwardCoeff G 1 * u ^ 2) 0 := by
    fun_prop
  have h₃ : AnalyticAt ℂ
      (thirdFaberCombinationFactor G α₁ α₂ α₃) 0 := by
    unfold thirdFaberCombinationFactor
    fun_prop
  rw [fourthFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ α₄,
    show k + 3 = (k + 2) + 1 by omega,
    actualTaylorCoeff_var_mul_succ _ h₃ (k + 2),
    thirdFaberCombinationFactor_actual_coeff G hc α₁ α₂ α₃ (k + 2)]
  rw [actualTaylorCoeff_var_sq_mul_succ_succ _ hφ k,
    show k + 2 = (k + 1) + 1 by omega,
    actualTaylorCoeff_var_mul_succ _ h₂ (k + 1)]

theorem exteriorPhi_actualCoeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    actualTaylorCoeff (exteriorPhi (rescaleExterior s F)) j =
      (s : ℂ) ^ j * actualTaylorCoeff (exteriorPhi F) j := by
  have h := congrArg (PowerSeries.coeff j)
    (exteriorPhi_actualTaylorSeries_rescale F hc hs0 hs1)
  simpa only [actualTaylorSeries_coeff,
    PowerSeries.coeff_rescale] using h

theorem secondFaberFactor_actualCoeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi (rescaleExterior s F) u ^ 2 -
        2 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2) j =
      (s : ℂ) ^ j * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) j := by
  have h := congrArg (PowerSeries.coeff j)
    (secondFaberFactor_actualTaylorSeries_rescale F hc hs0 hs1)
  simpa only [actualTaylorSeries_coeff,
    PowerSeries.coeff_rescale] using h

theorem thirdFaberFactor_actualCoeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    actualTaylorCoeff (fun u : ℂ =>
      exteriorPhi (rescaleExterior s F) u ^ 3 -
        3 * exteriorForwardCoeff (rescaleExterior s F) 1 * u ^ 2 *
          exteriorPhi (rescaleExterior s F) u -
        3 * exteriorForwardCoeff (rescaleExterior s F) 2 * u ^ 3) j =
      (s : ℂ) ^ j * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi F u ^ 3 -
          3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
          3 * exteriorForwardCoeff F 2 * u ^ 3) j := by
  have h := congrArg (PowerSeries.coeff j)
    (thirdFaberFactor_actualTaylorSeries_rescale F hc hs0 hs1)
  simpa only [actualTaylorSeries_coeff,
    PowerSeries.coeff_rescale] using h

/-- Exact rescale formula for every negative mode of the full four-vector
combination. Each summand retains its own power of the regularization
parameter; replacing all four by a common power would be incorrect. -/
theorem fourthFaberCombinationFactor_actual_coeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ : ℂ) (k : ℕ) :
    actualTaylorCoeff
        (fourthFaberCombinationFactor (rescaleExterior s F)
          α₁ α₂ α₃ α₄) (k + 3) =
      α₁ * (s : ℂ) ^ k * actualTaylorCoeff (exteriorPhi F) k +
      α₂ * (s : ℂ) ^ (k + 1) * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) (k + 1) +
      α₃ * (s : ℂ) ^ (k + 2) * actualTaylorCoeff (fun u : ℂ =>
        exteriorPhi F u ^ 3 -
          3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
          3 * exteriorForwardCoeff F 2 * u ^ 3) (k + 2) +
      α₄ * (s : ℂ) ^ (k + 3) *
        actualTaylorCoeff (fourthFaberFactor F) (k + 3) := by
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  rw [fourthFaberCombinationFactor_actual_coeff_decomp
    (rescaleExterior s F) hcG α₁ α₂ α₃ α₄ k,
    exteriorPhi_actualCoeff_rescale F hc hs0 hs1 k,
    secondFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 1),
    thirdFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 2),
    fourthFaberFactor_actualCoeff_rescale F hc hs0 hs1 (k + 3)]
  ring

/-- Explicit finite expression for a four-vector Faber mode during
regularization. At `s=1` it is the genuine original-map Taylor mode. -/
noncomputable def fourthFaberModeAtScale
    (F : ℂ → ℂ) (α₁ α₂ α₃ α₄ : ℂ) (k : ℕ) (s : ℝ) : ℂ :=
  α₁ * (s : ℂ) ^ k * actualTaylorCoeff (exteriorPhi F) k +
  α₂ * (s : ℂ) ^ (k + 1) * actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 2 - 2 * exteriorForwardCoeff F 1 * u ^ 2) (k + 1) +
  α₃ * (s : ℂ) ^ (k + 2) * actualTaylorCoeff (fun u : ℂ =>
    exteriorPhi F u ^ 3 -
      3 * exteriorForwardCoeff F 1 * u ^ 2 * exteriorPhi F u -
      3 * exteriorForwardCoeff F 2 * u ^ 3) (k + 2) +
  α₄ * (s : ℂ) ^ (k + 3) *
    actualTaylorCoeff (fourthFaberFactor F) (k + 3)

theorem fourthFaberModeAtScale_eq_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (α₁ α₂ α₃ α₄ : ℂ) (k : ℕ) :
    fourthFaberModeAtScale F α₁ α₂ α₃ α₄ k s =
      actualTaylorCoeff
        (fourthFaberCombinationFactor (rescaleExterior s F)
          α₁ α₂ α₃ α₄) (k + 3) := by
  exact (fourthFaberCombinationFactor_actual_coeff_rescale
    F hc hs0 hs1 α₁ α₂ α₃ α₄ k).symm

theorem fourthFaberModeAtScale_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ α₄ : ℂ) (k : ℕ) :
    fourthFaberModeAtScale F α₁ α₂ α₃ α₄ k 1 =
      actualTaylorCoeff
        (fourthFaberCombinationFactor F α₁ α₂ α₃ α₄) (k + 3) := by
  rw [fourthFaberCombinationFactor_actual_coeff_decomp
    F hc α₁ α₂ α₃ α₄ k]
  simp [fourthFaberModeAtScale]

/-- Full four-polynomial Green-area bound for the original actual map,
with the regularization parameter and all boundary hypotheses removed. -/
theorem exterior_fourthFaber_all_vector_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (α₁ α₂ α₃ α₄ : ℂ) :
    let A := fourthFaberCombinationFactor F α₁ α₂ α₃ α₄
    ‖actualTaylorCoeff A 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff A 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff A 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff A 8‖ ^ 2 ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 := by
  let E : ℝ → ℝ := fun s =>
    ‖fourthFaberModeAtScale F α₁ α₂ α₃ α₄ 2 s‖ ^ 2 +
      2 * ‖fourthFaberModeAtScale F α₁ α₂ α₃ α₄ 3 s‖ ^ 2 +
      3 * ‖fourthFaberModeAtScale F α₁ α₂ α₃ α₄ 4 s‖ ^ 2 +
      4 * ‖fourthFaberModeAtScale F α₁ α₂ α₃ α₄ 5 s‖ ^ 2
  have hcont : Continuous E := by
    dsimp only [E, fourthFaberModeAtScale]
    fun_prop
  have hlim : Filter.Tendsto
      (fun n : ℕ => E (omittedScaleSeq n)) Filter.atTop (nhds (E 1)) :=
    hcont.continuousAt.tendsto.comp omittedScaleSeq_tendsto_one
  have hbound (n : ℕ) : E (omittedScaleSeq n) ≤
      ‖α₁‖ ^ 2 + 2 * ‖α₂‖ ^ 2 +
        3 * ‖α₃‖ ^ 2 + 4 * ‖α₄‖ ^ 2 := by
    have h := rescaleExterior_fourthFaber_all_vector_energy_le
      F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
      α₁ α₂ α₃ α₄
    change ‖actualTaylorCoeff
        (fourthFaberCombinationFactor
          (rescaleExterior (omittedScaleSeq n) F) α₁ α₂ α₃ α₄) 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff
          (fourthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F) α₁ α₂ α₃ α₄) 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff
          (fourthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F) α₁ α₂ α₃ α₄) 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff
          (fourthFaberCombinationFactor
            (rescaleExterior (omittedScaleSeq n) F) α₁ α₂ α₃ α₄) 8‖ ^ 2 ≤ _ at h
    rw [← fourthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ 2,
      ← fourthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ 3,
      ← fourthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ 4,
      ← fourthFaberModeAtScale_eq_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
        α₁ α₂ α₃ α₄ 5] at h
    exact h
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  dsimp only [E] at h
  rw [fourthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ 2,
    fourthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ 3,
    fourthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ 4,
    fourthFaberModeAtScale_one F hc α₁ α₂ α₃ α₄ 5] at h
  exact h

end SpringerLean
