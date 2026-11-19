import SpringerLean.Round17PointKernel

open MeasureTheory Set

namespace SpringerLean

/-- A continuous boundary curve has a jointly integrable compensated
vertical logarithm. No condition excludes intersections with the line. -/
theorem verticalCurveKernel_integrable
    (a : ℝ) (W : ℝ → ℂ) (hW : Continuous W) :
    Integrable (fun p : ℝ × ℝ => verticalPointKernel a (W p.1) p.2)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  haveI : IsFiniteMeasure μ := Real.isFiniteMeasure_restrict_Ioc 0 (2 * Real.pi)
  have hmeas : Measurable
      (fun p : ℝ × ℝ => verticalPointKernel a (W p.1) p.2) := by
    dsimp [verticalPointKernel, verticalLogRadial, verticalBaseSlope]
    fun_prop
  have hjoin : AEStronglyMeasurable
      (fun p : ℝ × ℝ => verticalPointKernel a (W p.1) p.2)
      (μ.prod volume) := hmeas.aestronglyMeasurable
  apply (integrable_prod_iff hjoin).2
  constructor
  · filter_upwards with θ
    exact verticalPointKernel_integrable a (W θ)
  · let K : ℝ := ∫ y : ℝ, ‖verticalBaseCurvature y‖
    let C : ℝ → ℝ := fun θ =>
      Real.pi * |(|a - (W θ).re|) - 1| + (W θ).im ^ 2 * K
    have hC : Continuous C := by
      dsimp [C]
      fun_prop
    have hCint : Integrable C μ := by
      have h := (hC.continuousOn.integrableOn_compact (μ := volume)
        (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))))
      exact h.mono_set Ioc_subset_Icc_self
    have houter : AEStronglyMeasurable
        (fun θ : ℝ => ∫ y : ℝ,
          ‖verticalPointKernel a (W θ) y‖) μ := hjoin.norm.integral_prod_right'
    apply Integrable.mono' hCint houter
    filter_upwards with θ
    change ‖∫ y : ℝ, ‖verticalPointKernel a (W θ) y‖‖ ≤ C θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    simpa only [C, K, Real.norm_eq_abs] using verticalPointKernel_abs_integral_le a (W θ)

/-- Fubini for any continuous curve, in the same oriented angle interval used
by `Real.circleAverage`. -/
theorem verticalCurveKernel_integral_swap
    (a : ℝ) (W : ℝ → ℂ) (hW : Continuous W) :
    (∫ y : ℝ, ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      verticalPointKernel a (W θ) y) =
      ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        (∫ y : ℝ, verticalPointKernel a (W θ) y) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  have h := integral_integral_swap
    (f := fun θ y : ℝ => verticalPointKernel a (W θ) y)
    (μ := μ) (ν := volume) (verticalCurveKernel_integrable a W hW)
  simpa only [μ] using h.symm

/-- Integrated compensated potential of any continuous boundary curve. -/
theorem verticalCurveKernel_integral (a : ℝ) (W : ℝ → ℂ)
    (hW : Continuous W) :
    (∫ y : ℝ, ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
      verticalPointKernel a (W θ) y) =
      Real.pi * (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        (|a - (W θ).re| - 1)) := by
  rw [verticalCurveKernel_integral_swap a W hW]
  have hpoint (θ : ℝ) :
      (∫ y : ℝ, verticalPointKernel a (W θ) y) =
        Real.pi * (|a - (W θ).re| - 1) :=
    verticalPointKernel_integral a (W θ)
  simp_rw [hpoint]
  rw [integral_const_mul]

end SpringerLean
