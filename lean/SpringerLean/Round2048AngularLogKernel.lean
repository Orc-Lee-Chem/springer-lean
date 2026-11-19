import Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation

open Real Set MeasureTheory

namespace SpringerLean

private noncomputable def angularLogKernel (g : ℝ → ℂ) (α β : ℝ) : ℝ :=
  Real.log ‖g β - circleMap 0 1 α‖

private theorem angularLogKernel_slice_integrable (g : ℝ → ℂ) (β : ℝ) :
    IntegrableOn (fun α => angularLogKernel g α β) (Ioc 0 (2 * π)) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mp
  simpa [angularLogKernel, norm_sub_rev, CircleIntegrable] using
    (circleIntegrable_log_norm_sub_const (a := g β) (c := 0) 1)

private theorem angularLogKernel_slice_integral (g : ℝ → ℂ) (β : ℝ) :
    (∫ α in Ioc 0 (2 * π), angularLogKernel g α β) =
      (2 * π) * Real.posLog ‖g β‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := g β)
  rw [circleAverage_def, intervalIntegral.integral_of_le two_pi_pos.le, smul_eq_mul] at h
  have h' := congrArg (fun a : ℝ => (2 * π) * a) h
  simpa [angularLogKernel, norm_sub_rev, ← mul_assoc, two_pi_pos.ne'] using h'

/-- The logarithmic angular kernel is integrable on the product of
the two angle intervals. Only continuity of the parametrized curve
is needed. This permits Fubini for a single smooth exterior circle. -/
private theorem angularLogKernel_integrable (g : ℝ → ℂ) (hg : Continuous g) :
    IntegrableOn (fun p : ℝ × ℝ => angularLogKernel g p.1 p.2)
      (Ioc 0 (2 * π) ×ˢ Ioc 0 (2 * π)) := by
  let J := Ioc (0 : ℝ) (2 * π)
  let μ : Measure ℝ := volume.restrict J
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (by
    dsimp [J]
    rw [Real.volume_Ioc]
    finiteness)
  have hm : Measurable (fun p : ℝ × ℝ => angularLogKernel g p.1 p.2) := by
    unfold angularLogKernel
    fun_prop
  have hbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ β ∈ J, ‖g β‖ ≤ B := by
    obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).image hg.norm).bddAbove
    refine ⟨max 0 M, le_max_left _ _, ?_⟩
    intro β hβ
    exact (hM ⟨β, Ioc_subset_Icc_self hβ, rfl⟩).trans (le_max_right _ _)
  obtain ⟨B, hB, hnorm⟩ := hbound
  have hmean : Integrable (fun β => ∫ α, ‖angularLogKernel g α β‖ ∂μ) μ := by
    apply Integrable.mono (integrable_const (2 * ((2 * π) * Real.log (B + 1))))
      (hm.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem (show MeasurableSet J from measurableSet_Ioc)] with β hβ
    have hnonneg : 0 ≤ ∫ α, ‖angularLogKernel g α β‖ ∂μ := by positivity
    have htotal : 0 ≤ ∫ α, angularLogKernel g α β ∂μ := by
      rw [show (∫ α, angularLogKernel g α β ∂μ) =
        (2 * π) * Real.posLog ‖g β‖ from angularLogKernel_slice_integral g β]
      exact mul_nonneg two_pi_pos.le posLog_nonneg
    have hpos : (∫ α, (angularLogKernel g α β)⁺ ∂μ) ≤
        (2 * π) * Real.log (B + 1) := by
      have hK (α : ℝ) : 0 ≤ (angularLogKernel g α β)⁺ := by simp [posPart]
      have hle (α : ℝ) : (angularLogKernel g α β)⁺ ≤ Real.log (B + 1) := by
        have hlog : 0 ≤ Real.log (B + 1) := Real.log_nonneg (by linarith)
        unfold angularLogKernel
        change max (Real.log ‖g β - circleMap 0 1 α‖) 0 ≤ _
        refine max_le ?_ hlog
        by_cases hz : g β - circleMap 0 1 α = 0
        · simpa [hz] using hlog
        · apply Real.log_le_log (norm_pos_iff.mpr hz)
          exact (norm_sub_le _ _).trans (by simpa using hnorm β hβ)
      have hh := integral_mono_of_nonneg (.of_forall hK)
        (integrable_const (Real.log (B + 1)) : Integrable _ μ) (.of_forall hle)
      rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ] at hh
      have hvol : volume.real J = 2 * π := by
        dsimp [J]
        rw [volume_real_Ioc_of_le two_pi_pos.le, sub_zero]
      rw [hvol] at hh
      exact hh
    have hf := integral_abs_eq_two_mul_integral_posPart_sub_integral
      (show Integrable (fun α => angularLogKernel g α β) μ from
        angularLogKernel_slice_integrable g β)
    have hconst : 0 ≤ 2 * ((2 * π) * Real.log (B + 1)) :=
      mul_nonneg (by norm_num) (mul_nonneg two_pi_pos.le
        (Real.log_nonneg (by linarith)))
    rw [norm_of_nonneg hnonneg, norm_of_nonneg hconst]
    simp only [Real.norm_eq_abs]
    linarith
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact (integrable_prod_iff' hm.aestronglyMeasurable).2
    ⟨.of_forall (angularLogKernel_slice_integrable g), hmean⟩

/-- The inner integral in the logarithmic angular swap is integrable
as a function of the test angle. -/
theorem angular_circle_log_potential_outer_integrable
    (g : ℝ → ℂ) (hg : Continuous g) :
    IntervalIntegrable (fun α => ∫ β in 0..2 * π,
      Real.log ‖g β - circleMap 0 1 α‖) volume 0 (2 * π) := by
  have hi := angularLogKernel_integrable g hg
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).mpr
  simpa only [IntegrableOn, angularLogKernel, intervalIntegral.integral_of_le two_pi_pos.le] using
    hi.integral_prod_left

/-- A circle of test points turns the logarithmic potential of a
continuous parametrized curve into an average of logarithmic radial
hinges. The diagonal singularities are handled by product integrability. -/
theorem angular_integral_circle_log_potential (g : ℝ → ℂ) (hg : Continuous g) :
    (∫ α in 0..2 * π, ∫ β in 0..2 * π,
      Real.log ‖g β - circleMap 0 1 α‖) =
    (2 * π) * (∫ β in 0..2 * π, Real.posLog ‖g β‖) := by
  change (∫ α in 0..2 * π, ∫ β in 0..2 * π, angularLogKernel g α β) = _
  rw [intervalIntegral_intervalIntegral_swap]
  · simp_rw [intervalIntegral.integral_of_le two_pi_pos.le,
      angularLogKernel_slice_integral g, integral_const_mul]
  · rw [uIoc_of_le two_pi_pos.le]
    have heq : Function.uncurry (angularLogKernel g) =
        (fun p : ℝ × ℝ => angularLogKernel g p.1 p.2) := by
      funext p
      cases p
      rfl
    rw [heq]
    exact angularLogKernel_integrable g hg

end SpringerLean
