import SpringerLean.Round17CurveDifference
import SpringerLean.Round15PositivePart

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual regularized boundary, rotated by a complex direction,
is a continuous angle-parametrized curve. -/
theorem regularExterior_rotated_angle_continuous
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    Continuous (fun θ : ℝ =>
      conj ξ * rescaleExterior s F (circleMap 0 1 θ)) := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : ContinuousOn (rescaleExterior s F) (sphere (0 : ℂ) 1) := by
    intro z hz
    have hnorm : ‖z‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hz
    have hext : z ∈ exteriorAbove s := by
      change s < ‖z‖
      rw [hnorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hext).continuousAt.continuousWithinAt
  have hmem (θ : ℝ) : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := by
    simp [mem_sphere, dist_zero_right, norm_circleMap_zero]
  exact continuous_const.mul
    (hG.comp_continuous (continuous_circleMap 0 1) hmem)

theorem comparisonCircle_angle_continuous :
    Continuous (fun θ : ℝ =>
      ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ)) := by
  fun_prop

/-- The full-line identity for the compensated potentials of the actual
regularized boundary and the comparison circle, before normalization. -/
theorem regularExterior_compensated_vertical_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    (∫ y : ℝ,
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a
          (conj ξ * rescaleExterior s F (circleMap 0 1 θ)) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a
          ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ) y)) =
      Real.pi * (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        (|a - (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re| -
          |a - 2 * (circleMap 0 1 θ).re|)) := by
  simpa only [Complex.ofReal_re] using
    (verticalCurveKernel_difference_integral a
      (fun θ : ℝ => conj ξ * rescaleExterior s F (circleMap 0 1 θ))
      (fun θ : ℝ => ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ))
      (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
      comparisonCircle_angle_continuous)

/-- The integrand in the preceding actual-curve identity is L¹ on the
whole vertical line. -/
theorem regularExterior_compensated_vertical_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    Integrable (fun y : ℝ =>
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a
          (conj ξ * rescaleExterior s F (circleMap 0 1 θ)) y) -
      (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
        verticalPointKernel a
          ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ) y)) := by
  exact verticalCurveKernel_difference_integrable a
    (fun θ : ℝ => conj ξ * rescaleExterior s F (circleMap 0 1 θ))
    (fun θ : ℝ => ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ))
    (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
    comparisonCircle_angle_continuous

/-- A circle average is an integral over the actual half-open angle interval. -/
theorem circleAverage_eq_angle_Ioc (f : ℂ → ℝ) :
    Real.circleAverage f 0 1 =
      (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), f (circleMap 0 1 θ)) := by
  rw [Real.circleAverage_def,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  rfl

/-- The normalized compensated vertical formula already has the two
actual projected circle averages on its right-hand side. -/
theorem regularExterior_compensated_vertical_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    (∫ y : ℝ,
      (2 * Real.pi)⁻¹ *
        ((∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          verticalPointKernel a
            (conj ξ * rescaleExterior s F (circleMap 0 1 θ)) y) -
         (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          verticalPointKernel a
            ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ) y))) =
      Real.pi *
        (Real.circleAverage
          (fun ζ : ℂ => |a - (conj ξ * rescaleExterior s F ζ).re|) 0 1 -
         Real.circleAverage (fun ζ : ℂ => |a - 2 * ζ.re|) 0 1) := by
  rw [integral_const_mul,
    regularExterior_compensated_vertical_integral F hc hs0 hs1 ξ a]
  rw [circleAverage_eq_angle_Ioc, circleAverage_eq_angle_Ioc]
  have hW : IntegrableOn
      (fun θ : ℝ => |a - (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re|)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
    have h : Continuous (fun θ : ℝ =>
        |a - (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re|) := by
      exact (continuous_const.sub
        (Complex.continuous_re.comp
          (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ))).abs
    exact (h.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  have hV : IntegrableOn (fun θ : ℝ => |a - 2 * (circleMap 0 1 θ).re|)
      (Ioc (0 : ℝ) (2 * Real.pi)) := by
    have h : Continuous (fun θ : ℝ => |a - 2 * (circleMap 0 1 θ).re|) := by fun_prop
    exact (h.continuousOn.integrableOn_compact (μ := volume)
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi)))).mono_set Ioc_subset_Icc_self
  rw [integral_sub hW hV]
  ring

end SpringerLean
