import SpringerLean.Round17CurveKernel

open MeasureTheory Set

namespace SpringerLean

/-- The difference of compensated curve potentials is absolutely integrable
on the entire vertical line. -/
theorem verticalCurveKernel_difference_integrable
    (a : ℝ) (W V : ℝ → ℂ) (hW : Continuous W) (hV : Continuous V) :
    Integrable (fun y : ℝ =>
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (W θ) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (V θ) y)) := by
  have hWi := (verticalCurveKernel_integrable a W hW).integral_prod_right
  have hVi := (verticalCurveKernel_integrable a V hV).integral_prod_right
  exact hWi.sub hVi

/-- A fully compensated vertical-line formula for two continuous curves.
The angle interval has total length `2π`; the common base logarithm cancels. -/
theorem verticalCurveKernel_difference_integral
    (a : ℝ) (W V : ℝ → ℂ) (hW : Continuous W) (hV : Continuous V) :
    (∫ y : ℝ,
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (W θ) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), verticalPointKernel a (V θ) y)) =
      Real.pi * (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        (|a - (W θ).re| - |a - (V θ).re|)) := by
  have hWi := (verticalCurveKernel_integrable a W hW).integral_prod_right
  have hVi := (verticalCurveKernel_integrable a V hV).integral_prod_right
  rw [integral_sub hWi hVi,
    verticalCurveKernel_integral a W hW,
    verticalCurveKernel_integral a V hV]
  have hleft : IntegrableOn (fun θ : ℝ => |a - (W θ).re| - 1)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
    have h : Continuous (fun θ : ℝ => |a - (W θ).re| - 1) := by fun_prop
    exact (h.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hright : IntegrableOn (fun θ : ℝ => |a - (V θ).re| - 1)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
    have h : Continuous (fun θ : ℝ => |a - (V θ).re| - 1) := by fun_prop
    exact (h.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  rw [← mul_sub, ← integral_sub hleft hright]
  congr 1
  apply integral_congr_ae
  filter_upwards with θ
  ring

end SpringerLean
