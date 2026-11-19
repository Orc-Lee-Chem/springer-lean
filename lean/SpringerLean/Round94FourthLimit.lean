import SpringerLean.Round93FourthModes

set_option maxHeartbeats 500000

namespace SpringerLean

/-- The complete fourth reciprocal Faber factor of one actual exterior map. -/
noncomputable def fourthFaberFactor (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  (exteriorPhi F u) ^ 4 -
    4 * exteriorForwardCoeff F 1 * u ^ 2 * (exteriorPhi F u) ^ 2 -
    4 * exteriorForwardCoeff F 2 * u ^ 3 * exteriorPhi F u -
    (4 * exteriorForwardCoeff F 3 -
      2 * (exteriorForwardCoeff F 1) ^ 2) * u ^ 4

/-- Exterior regularization rescales every formal forward coefficient with
the exact paper power `s^(j+1)`. -/
theorem exteriorFormalForward_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    exteriorFormalForward (rescaleExterior s F) =
      PowerSeries.C (s : ℂ) *
        PowerSeries.rescale (s : ℂ) (exteriorFormalForward F) := by
  apply PowerSeries.ext
  intro j
  simp only [exteriorFormalForward_coeff,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  rw [rescaleExterior_forwardCoeff F hc hs0]
  ring

/-- Consequently the actual regularized forward factor is the formal
rescaling of the original factor, not a new independent series. -/
theorem formalExteriorPhi_rescale_exterior
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) :
    formalExteriorPhi (exteriorFormalForward (rescaleExterior s F)) =
      PowerSeries.rescale (s : ℂ)
        (formalExteriorPhi (exteriorFormalForward F)) := by
  rw [exteriorFormalForward_rescale F hc hs0]
  simp only [formalExteriorPhi, map_add, map_one, map_mul,
    PowerSeries.rescale_X]
  ring

private theorem fourth_rescale_C (s a : ℂ) :
    PowerSeries.rescale s (PowerSeries.C a) = PowerSeries.C a := by
  apply PowerSeries.ext
  intro j
  simp only [PowerSeries.coeff_rescale]
  by_cases hj : j = 0
  · subst j
    simp
  · simp [PowerSeries.coeff_C, hj]

/-- All fourth-Faber Taylor coefficients of the regularized actual map
scale by `s^j`; this applies to the entire analytic factor, not merely its
first few terms. -/
theorem fourthFaberFactor_actualTaylorSeries_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    actualTaylorSeries (fourthFaberFactor (rescaleExterior s F)) =
      PowerSeries.rescale (s : ℂ)
        (actualTaylorSeries (fourthFaberFactor F)) := by
  let G := rescaleExterior s F
  let φ := formalExteriorPhi (exteriorFormalForward F)
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have hG := fourthFaberFactor_actualTaylorSeries G hcG
  have hF := fourthFaberFactor_actualTaylorSeries F hc
  change actualTaylorSeries (fourthFaberFactor G) = _ at hG
  change actualTaylorSeries (fourthFaberFactor F) = _ at hF
  rw [hG, hF]
  dsimp only [G]
  simp only [formalExteriorPhi_rescale_exterior F hc hs0,
    rescaleExterior_forwardCoeff F hc hs0,
    map_sub, map_pow, map_mul,
    PowerSeries.rescale_X,
    fourth_rescale_C]
  ring

theorem fourthFaberFactor_actualCoeff_rescale
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    actualTaylorCoeff (fourthFaberFactor (rescaleExterior s F)) j =
      (s : ℂ) ^ j * actualTaylorCoeff (fourthFaberFactor F) j := by
  have h := congrArg (PowerSeries.coeff j)
    (fourthFaberFactor_actualTaylorSeries_rescale F hc hs0 hs1)
  simpa only [actualTaylorSeries_coeff,
    PowerSeries.coeff_rescale] using h

/-- The fourth Faber weighted negative-mode area inequality for the
unregularized, actual map in the manuscript class. The limit uses the
exact all-coefficient scaling above, so no boundary regularity assumption
is introduced at `|z|=1`. -/
theorem exterior_fourthFaber_actual_mode_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖actualTaylorCoeff (fourthFaberFactor F) 5‖ ^ 2 +
        2 * ‖actualTaylorCoeff (fourthFaberFactor F) 6‖ ^ 2 +
        3 * ‖actualTaylorCoeff (fourthFaberFactor F) 7‖ ^ 2 +
        4 * ‖actualTaylorCoeff (fourthFaberFactor F) 8‖ ^ 2 ≤ 4 := by
  let E : ℝ → ℝ := fun s =>
    ‖(s : ℂ) ^ 5 * actualTaylorCoeff (fourthFaberFactor F) 5‖ ^ 2 +
      2 * ‖(s : ℂ) ^ 6 * actualTaylorCoeff (fourthFaberFactor F) 6‖ ^ 2 +
      3 * ‖(s : ℂ) ^ 7 * actualTaylorCoeff (fourthFaberFactor F) 7‖ ^ 2 +
      4 * ‖(s : ℂ) ^ 8 * actualTaylorCoeff (fourthFaberFactor F) 8‖ ^ 2
  have hcont : Continuous E := by
    dsimp only [E]
    fun_prop
  have hlim : Filter.Tendsto
      (fun n : ℕ => E (omittedScaleSeq n)) Filter.atTop (nhds (E 1)) :=
    hcont.continuousAt.tendsto.comp omittedScaleSeq_tendsto_one
  have hbound (n : ℕ) : E (omittedScaleSeq n) ≤ 4 := by
    have h := fourthFaber_actual_mode_energy_le F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
    change
      ‖actualTaylorCoeff
        (fourthFaberFactor (rescaleExterior (omittedScaleSeq n) F)) 5‖ ^ 2 +
          2 * ‖actualTaylorCoeff
            (fourthFaberFactor (rescaleExterior (omittedScaleSeq n) F)) 6‖ ^ 2 +
          3 * ‖actualTaylorCoeff
            (fourthFaberFactor (rescaleExterior (omittedScaleSeq n) F)) 7‖ ^ 2 +
          4 * ‖actualTaylorCoeff
            (fourthFaberFactor (rescaleExterior (omittedScaleSeq n) F)) 8‖ ^ 2 ≤
        4 at h
    rw [fourthFaberFactor_actualCoeff_rescale F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) 5,
      fourthFaberFactor_actualCoeff_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) 6,
      fourthFaberFactor_actualCoeff_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) 7,
      fourthFaberFactor_actualCoeff_rescale F hc
        (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) 8] at h
    exact h
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  simpa only [E, Complex.ofReal_one, one_pow, one_mul] using h

end SpringerLean
