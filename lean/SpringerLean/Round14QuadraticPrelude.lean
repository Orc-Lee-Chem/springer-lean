import SpringerLean.Round13Semicircle
import Mathlib.Analysis.Complex.MeanValue

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Analytic reflection of an actual projected harmonic filling. -/
noncomputable def projectionAnalytic (F : ℂ → ℂ) (c u : ℂ) : ℂ :=
  conj c * u + c * exteriorForwardGerm F u

@[simp] theorem projectionAnalytic_zero (F : ℂ → ℂ) (c : ℂ) :
    projectionAnalytic F c 0 = 0 := by
  simp [projectionAnalytic, exteriorForwardGerm_zero]

/-- On reflected points, the projected actual filling is the real part of
one analytic function on the whole disk. -/
theorem actualHarmonic_projection_reflection (F : ℂ → ℂ) (c u : ℂ) :
    (c * actualHarmonic F (conj u)).re = (projectionAnalytic F c u).re := by
  simp only [actualHarmonic, Complex.conj_conj, mul_add, projectionAnalytic,
    Complex.add_re]
  congr 1
  rw [← Complex.conj_re (conj c * u)]
  simp

theorem projectionAnalytic_analyticOnNhd (F : ℂ → ℂ)
    (hc : CenteredExteriorUnivalent F) (c : ℂ) :
    AnalyticOnNhd ℂ (projectionAnalytic F c) (ball 0 1) := by
  intro u hu
  have hG := exteriorForwardGerm_analyticOnNhd_unitBall F hc u hu
  change AnalyticAt ℂ (fun v => conj c * v + c * exteriorForwardGerm F v) u
  fun_prop

/-- Its square has zero normalized circle mean on every smaller circle. -/
theorem projectionAnalytic_sq_circleAverage_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun u : ℂ => projectionAnalytic F c u ^ 2) 0 r = 0 := by
  have hAnal := (projectionAnalytic_analyticOnNhd F hc c).pow 2
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    intro u hu
    rw [abs_of_nonneg hr0] at hu
    exact lt_of_le_of_lt hu hr1
  have hcont : ContinuousOn (fun u : ℂ => projectionAnalytic F c u ^ 2)
      (closedBall (0 : ℂ) |r|) := hAnal.continuousOn.mono hsub
  have hdiff : ∀ u ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun v : ℂ => projectionAnalytic F c v ^ 2) u := by
    intro u hu
    exact (hAnal u (hsub (ball_subset_closedBall hu.1))).differentiableAt
  simpa only [projectionAnalytic_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    (circleAverage_of_differentiable_on_off_countable
      (s := (∅ : Set ℂ)) Set.countable_empty hcont hdiff)


/-- The actual forward-germ Taylor polynomials converge uniformly on every
strictly smaller open disk. This is the circle Parseval bridge. -/
theorem exteriorForwardGerm_uniform_on_subdisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : NNReal} (hr : (r : ℝ) < 1) :
    TendstoUniformlyOn
      (fun M u => ∑ j ∈ Finset.range M, exteriorForwardCoeff F j * u ^ j)
      (exteriorForwardGerm F) Filter.atTop
      (ball (0 : ℂ) (r : ℝ)) := by
  let f := exteriorForwardGerm F
  let c : ℕ → ℂ := exteriorForwardCoeff F
  have hr1 : r < (1 : NNReal) := by exact_mod_cast hr
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hRpos : (0 : NNReal) < R := lt_of_le_of_lt (zero_le : 0 ≤ r) hrR
  have hRreal : (R : ℝ) < 1 := by exact_mod_cast hR1
  have hd : DifferentiableOn ℂ f (closedBall 0 R) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).differentiableOn.mono
      (closedBall_subset_ball hRreal)
  have hp := hd.hasFPowerSeriesOnBall hRpos
  have hlocal : ∀ᶠ u in nhds (0 : ℂ),
      HasSum (fun j => c j * u ^ j) (f u) := by
    filter_upwards [ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1)] with u hu
    exact exteriorForwardGerm_hasSum_coeff_unitBall F hc
      (by simpa only [mem_ball, dist_zero_right] using hu)
  have hpCoeff : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [hlocal] with u hu
    simpa [FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hu
  have hEq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hpCoeff
  rw [hEq] at hp
  have hrad : (r : ENNReal) < (R : ENNReal) := by exact_mod_cast hrR
  have huniform := hp.tendstoUniformlyOn hrad
  simpa [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.coeff_ofScalars,
    f, c, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using huniform
end SpringerLean