import SpringerLean.Round17LogDifference

open MeasureTheory Filter
open scoped Topology

namespace SpringerLean

/-- First and second real derivatives of the base logarithm `L₁`. -/
noncomputable def verticalBaseSlope (y : ℝ) : ℝ := y / (1 + y ^ 2)
noncomputable def verticalBaseCurvature (y : ℝ) : ℝ := (1 - y ^ 2) / (1 + y ^ 2) ^ 2

theorem verticalLogRadial_one_hasDerivAt (y : ℝ) :
    HasDerivAt (verticalLogRadial 1) (verticalBaseSlope y) y := by
  have hquad : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * y) y := by
    convert (hasDerivAt_pow 2 y).const_add 1 using 1 <;> ring
  have h := (hquad.log (by positivity : 1 + y ^ 2 ≠ 0)).div_const 2
  convert h using 1
  · funext x
    simp [verticalLogRadial]
    ring
  · simp [verticalBaseSlope]
    ring

theorem verticalBaseSlope_hasDerivAt (y : ℝ) :
    HasDerivAt verticalBaseSlope (verticalBaseCurvature y) y := by
  have hquad : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * y) y := by
    convert (hasDerivAt_pow 2 y).const_add 1 using 1 <;> ring
  have h := (hasDerivAt_id y).div hquad (by positivity : 1 + y ^ 2 ≠ 0)
  convert h using 1
  · funext x
    rfl
  · dsimp [verticalBaseCurvature]
    field_simp
    ring

theorem verticalBaseSlope_continuous : Continuous verticalBaseSlope :=
  continuous_iff_continuousAt.mpr
    (fun y => (verticalBaseSlope_hasDerivAt y).continuousAt)

theorem verticalBaseCurvature_continuous : Continuous verticalBaseCurvature := by
  unfold verticalBaseCurvature
  have hnum : Continuous (fun y : ℝ => 1 - y ^ 2) := by fun_prop
  have hden : Continuous (fun y : ℝ => (1 + y ^ 2) ^ 2) := by fun_prop
  exact hnum.div hden (fun y => by positivity)

theorem verticalLogRadial_one_continuous : Continuous (verticalLogRadial 1) :=
  continuous_iff_continuousAt.mpr
    (fun y => (verticalLogRadial_one_hasDerivAt y).continuousAt)

theorem verticalBaseCurvature_norm_le (y : ℝ) :
    ‖verticalBaseCurvature y‖ ≤ (1 + y ^ 2)⁻¹ := by
  have hden : 0 < 1 + y ^ 2 := by positivity
  have habs : |1 - y ^ 2| ≤ 1 + y ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg y]
  rw [Real.norm_eq_abs]
  dsimp [verticalBaseCurvature]
  rw [abs_div, abs_of_pos (sq_pos_of_pos hden)]
  calc
    |1 - y ^ 2| / (1 + y ^ 2) ^ 2 ≤
        (1 + y ^ 2) / (1 + y ^ 2) ^ 2 :=
      (div_le_div_iff_of_pos_right (sq_pos_of_pos hden)).mpr habs
    _ = (1 + y ^ 2)⁻¹ := by field_simp

theorem verticalBaseCurvature_integrable : Integrable verticalBaseCurvature := by
  have hmeas : AEStronglyMeasurable verticalBaseCurvature volume := by
    have h : Measurable verticalBaseCurvature := by
      unfold verticalBaseCurvature
      measurability
    exact h.aestronglyMeasurable
  apply Integrable.mono' integrable_inv_one_add_sq hmeas
  exact Filter.Eventually.of_forall verticalBaseCurvature_norm_le

private theorem verticalBaseSlope_tendsto_zero_of_inv
    {l : Filter ℝ} (hinv : Filter.Tendsto (fun y : ℝ => y⁻¹) l (nhds 0))
    (hnev : ∀ᶠ y : ℝ in l, y ≠ 0) :
    Filter.Tendsto verticalBaseSlope l (nhds 0) := by
  have hcont : ContinuousAt (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 := by
    have hden : ContinuousAt (fun x : ℝ => 1 + x ^ 2) 0 := by fun_prop
    exact hden.inv₀ (by norm_num)
  have hfac : Filter.Tendsto
      (fun y : ℝ => y⁻¹ * (1 + (y⁻¹) ^ 2)⁻¹) l (nhds 0) := by
    simpa using hinv.mul (hcont.tendsto.comp hinv)
  refine hfac.congr' ?_
  filter_upwards [hnev] with y hy
  dsimp [verticalBaseSlope]
  field_simp [hy]
  ring

theorem verticalBaseSlope_tendsto_atTop_zero :
    Filter.Tendsto verticalBaseSlope Filter.atTop (nhds 0) := by
  apply verticalBaseSlope_tendsto_zero_of_inv tendsto_inv_atTop_zero
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact ne_of_gt hy

theorem verticalBaseSlope_tendsto_atBot_zero :
    Filter.Tendsto verticalBaseSlope Filter.atBot (nhds 0) := by
  apply verticalBaseSlope_tendsto_zero_of_inv tendsto_inv_atBot_zero
  filter_upwards [eventually_lt_atBot (0 : ℝ)] with y hy
  exact ne_of_lt hy

theorem verticalBaseCurvature_integral_zero :
    ∫ y : ℝ, verticalBaseCurvature y = 0 := by
  simpa using integral_of_hasDerivAt_of_tendsto
    verticalBaseSlope_hasDerivAt verticalBaseCurvature_integrable
    verticalBaseSlope_tendsto_atBot_zero verticalBaseSlope_tendsto_atTop_zero

theorem verticalBaseCurvature_shift_integrable (c : ℝ) :
    Integrable (fun y : ℝ => verticalBaseCurvature (y - c)) := by
  simpa only [sub_eq_add_neg, add_comm] using
    verticalBaseCurvature_integrable.comp_add_left (-c)

theorem verticalBaseCurvature_shift_integral_zero (c : ℝ) :
    ∫ y : ℝ, verticalBaseCurvature (y - c) = 0 := by
  rw [show (fun y : ℝ => verticalBaseCurvature (y - c)) =
      (fun y => verticalBaseCurvature (y + -c)) by funext y; ring]
  rw [integral_add_right_eq_self verticalBaseCurvature (-c),
    verticalBaseCurvature_integral_zero]

end SpringerLean
