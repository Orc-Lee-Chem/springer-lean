import SpringerLean.CircleDerivative

open scoped Topology NNReal ENNReal

namespace SpringerLean

/-- The derivative Taylor partial sums of the actual forward germ converge
uniformly on every disk strictly inside the unit disk. -/
theorem exteriorForwardGerm_deriv_uniform_on_subdisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ≥0} (hr : (r : ℝ) < 1) :
    TendstoUniformlyOn
      (fun M u => ∑ j ∈ Finset.range M,
        (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1) * u ^ j)
      (deriv (exteriorForwardGerm F)) Filter.atTop
      (Metric.ball (0 : ℂ) r) := by
  let f := deriv (exteriorForwardGerm F)
  let c : ℕ → ℂ := fun j =>
    (j + 1 : ℂ) * exteriorForwardCoeff F (j + 1)
  have hr1 : r < (1 : ℝ≥0) := by exact_mod_cast hr
  obtain ⟨R, hrR, hR1⟩ := exists_between hr1
  have hRpos : (0 : ℝ≥0) < R := lt_of_le_of_lt (zero_le : 0 ≤ r) hrR
  have hRreal : (R : ℝ) < 1 := by exact_mod_cast hR1
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.differentiableOn.mono
      (Metric.closedBall_subset_ball hRreal)
  have hp := hd.hasFPowerSeriesOnBall hRpos
  have hlocal : ∀ᶠ u in 𝓝 (0 : ℂ),
      HasSum (fun j => c j * u ^ j) (f u) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1)] with u hu
    exact exteriorForwardGerm_deriv_hasSum_coeff_unitBall F hc
      (by simpa only [Metric.mem_ball, dist_zero_right] using hu)
  have hpCoeff : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [hlocal] with u hu
    simpa [FormalMultilinearSeries.coeff_ofScalars,
      smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hu
  have hEq := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries hpCoeff
  rw [hEq] at hp
  have hrad : (r : ℝ≥0∞) < (R : ℝ≥0∞) := by exact_mod_cast hrR
  have huniform := hp.tendstoUniformlyOn hrad
  simpa [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.coeff_ofScalars,
    f, c, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    using huniform

end SpringerLean
