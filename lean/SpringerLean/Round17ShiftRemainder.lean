import SpringerLean.Round17ShiftDerivative

open MeasureTheory

namespace SpringerLean

/-- The imaginary-translation correction of the base logarithm. -/
noncomputable def verticalShiftRemainder (c y : ℝ) : ℝ :=
  verticalLogRadial 1 (y - c) - verticalLogRadial 1 y +
    c * verticalBaseSlope y

/-- Exact integral remainder for translation of the base logarithm.
The oriented interval covers positive and negative imaginary shifts. -/
theorem verticalShiftRemainder_eq_intervalIntegral (c y : ℝ) :
    verticalShiftRemainder c y =
      ∫ t : ℝ in (0 : ℝ)..c,
        (c - t) * verticalBaseCurvature (y - t) := by
  let P : ℝ → ℝ := fun t => verticalLogRadial 1 (y - t) -
    (c - t) * verticalBaseSlope (y - t)
  have hPder (t : ℝ) : HasDerivAt P
      ((c - t) * verticalBaseCurvature (y - t)) t := by
    have hshift : HasDerivAt (fun u : ℝ => y - u) (-1) t := by
      have h := (hasDerivAt_const t y).sub (hasDerivAt_id t)
      have hfun : ((fun _ : ℝ => y) - id) = (fun u : ℝ => y - u) := by
        funext u
        rfl
      rw [hfun] at h
      simpa using h
    have hcsub : HasDerivAt (fun u : ℝ => c - u) (-1) t := by
      have h := (hasDerivAt_const t c).sub (hasDerivAt_id t)
      have hfun : ((fun _ : ℝ => c) - id) = (fun u : ℝ => c - u) := by
        funext u
        rfl
      rw [hfun] at h
      simpa using h
    have hk := (verticalLogRadial_one_hasDerivAt (y - t)).comp t hshift
    have hq := (verticalBaseSlope_hasDerivAt (y - t)).comp t hshift
    have hp := hcsub.mul hq
    change HasDerivAt
      (fun u => verticalLogRadial 1 (y - u) -
        (c - u) * verticalBaseSlope (y - u))
      ((c - t) * verticalBaseCurvature (y - t)) t
    convert hk.sub hp using 1
    · funext u
      rfl
    · simp only [Function.comp_def]
      ring
  have hcont : Continuous
      (fun t : ℝ => (c - t) * verticalBaseCurvature (y - t)) := by
    exact (continuous_const.sub continuous_id).mul
      (verticalBaseCurvature_continuous.comp (continuous_const.sub continuous_id))
  have hFTC :
      (∫ t : ℝ in (0 : ℝ)..c,
        (c - t) * verticalBaseCurvature (y - t)) = P c - P 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t _
      exact hPder t
    · exact hcont.intervalIntegrable _ _
  rw [hFTC]
  simp [P, verticalShiftRemainder]
  ring

end SpringerLean
