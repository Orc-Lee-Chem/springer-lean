import SpringerLean.Round29LogQuadratic

open MeasureTheory Set Metric

namespace SpringerLean

/-- Averaging a bounded zero-mean complex boundary source cancels the
linear logarithmic term and leaves a quadratic far-field error. -/
theorem circleAverage_log_norm_sub_far_of_mean_zero
    (W : ℂ → ℂ)
    (hW : ContinuousOn W (sphere (0 : ℂ) 1))
    (hmean : Real.circleAverage W 0 1 = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖W ζ‖ ≤ B)
    (z : ℂ) (hz : 2 * B < ‖z‖) :
    |Real.circleAverage (fun ζ : ℂ => Real.log ‖z - W ζ‖) 0 1 -
      Real.log ‖z‖| ≤ B ^ 2 / ‖z‖ ^ 2 := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hzn : z ≠ 0 := norm_pos_iff.mp hzpos
  let S : Set ℂ := sphere (0 : ℂ) 1
  let f : ℂ → ℝ := fun ζ => Real.log ‖z - W ζ‖
  let l : ℂ → ℝ := fun ζ => (W ζ / z).re
  let e : ℂ → ℝ := fun ζ => f ζ - Real.log ‖z‖ + l ζ
  have hnonzero (ζ : ℂ) (hζ : ζ ∈ S) : z - W ζ ≠ 0 := by
    intro heq
    have heq' : z = W ζ := sub_eq_zero.mp heq
    have := hbound ζ hζ
    rw [← heq'] at this
    linarith
  have hfcont : ContinuousOn f S := by
    apply ContinuousOn.log ((continuousOn_const.sub hW).norm)
    intro ζ hζ
    exact (norm_pos_iff.mpr (hnonzero ζ hζ)).ne'
  have hlcont : ContinuousOn l S := by
    dsimp [l]
    exact Complex.continuous_re.comp_continuousOn (hW.div_const z)
  have hecont : ContinuousOn e S := (hfcont.sub continuousOn_const).add hlcont
  have hfci : CircleIntegrable f 0 1 := hfcont.circleIntegrable (by norm_num)
  have hlci : CircleIntegrable l 0 1 := hlcont.circleIntegrable (by norm_num)
  have heci : CircleIntegrable e 0 1 := hecont.circleIntegrable (by norm_num)
  have heabsci : CircleIntegrable (fun ζ => |e ζ|) 0 1 :=
    hecont.abs.circleIntegrable (by norm_num)
  have hbounde (ζ : ℂ) (hζ : ζ ∈ S) : |e ζ| ≤ B ^ 2 / ‖z‖ ^ 2 := by
    have hfar : 2 * ‖W ζ‖ ≤ ‖z‖ := by linarith [hbound ζ hζ]
    have hr := log_norm_sub_far_quadratic z (W ζ) hzn hfar
    have hsq : ‖W ζ‖ ^ 2 ≤ B ^ 2 := (sq_le_sq).2 (by
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hB]
      exact hbound ζ hζ)
    exact hr.trans (div_le_div_of_nonneg_right hsq (sq_nonneg _))
  have heavg : |Real.circleAverage e 0 1| ≤ B ^ 2 / ‖z‖ ^ 2 := by
    calc
      |Real.circleAverage e 0 1| ≤
          Real.circleAverage (fun ζ => |e ζ|) 0 1 :=
        Real.abs_circleAverage_le_circleAverage_abs
      _ ≤ B ^ 2 / ‖z‖ ^ 2 :=
        Real.circleAverage_mono_on_of_le_circle heabsci (by
          intro ζ hζ
          exact hbounde ζ (by simpa [S] using hζ))
  have hWci : CircleIntegrable W 0 1 := hW.circleIntegrable (by norm_num)
  have hWdiv : CircleIntegrable (fun ζ => W ζ / z) 0 1 :=
    (hW.div_const z).circleIntegrable (by norm_num)
  have hdivavg : Real.circleAverage (fun ζ => W ζ / z) 0 1 = 0 := by
    calc
      Real.circleAverage (fun ζ => W ζ / z) 0 1 =
        z⁻¹ • Real.circleAverage W 0 1 := by
          simpa only [div_eq_mul_inv, smul_eq_mul, mul_comm] using
            (Real.circleAverage_fun_smul (a := z⁻¹) (f := W) (c := 0) (R := 1))
      _ = 0 := by rw [hmean]; simp
  have hlavg : Real.circleAverage l 0 1 = 0 := by
    have hmap := Complex.reCLM.circleAverage_comp_comm hWdiv
    have hmap' : Real.circleAverage l 0 1 =
        (Real.circleAverage (fun ζ => W ζ / z) 0 1).re := by
      simpa only [Function.comp_def, Complex.reCLM_apply, l] using hmap
    rw [hmap', hdivavg]
    rfl
  have hcst : CircleIntegrable (fun _ : ℂ => Real.log ‖z‖) 0 1 :=
    continuousOn_const.circleIntegrable (by norm_num)
  have heqavg : Real.circleAverage e 0 1 =
      Real.circleAverage f 0 1 - Real.log ‖z‖ := by
    change Real.circleAverage ((f - fun _ : ℂ => Real.log ‖z‖) + l) 0 1 = _
    rw [Real.circleAverage_add (hfci.sub hcst) hlci]
    rw [Real.circleAverage_sub hfci hcst]
    rw [Real.circleAverage_const, hlavg]
    ring
  rw [heqavg] at heavg
  exact heavg
end SpringerLean