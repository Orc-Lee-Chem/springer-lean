import SpringerLean.Round18SignReduction
import SpringerLean.Round17ActualCurve

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Equal-mean projections have equal absolute-deviation averages beyond
both of their upper ranges. -/
theorem circleAverage_abs_diff_zero_of_upper
    (X Y : ℂ → ℝ) (a : ℝ)
    (hX : CircleIntegrable X 0 1) (hY : CircleIntegrable Y 0 1)
    (hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1)
    (hXupper : ∀ ζ ∈ sphere (0 : ℂ) 1, X ζ ≤ a)
    (hYupper : ∀ ζ ∈ sphere (0 : ℂ) 1, Y ζ ≤ a) :
    Real.circleAverage (fun ζ => |a - X ζ|) 0 1 -
      Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 = 0 := by
  have hXA : Real.circleAverage (fun ζ => |a - X ζ|) 0 1 =
      Real.circleAverage (fun ζ => a - X ζ) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    exact abs_of_nonneg (sub_nonneg.mpr (hXupper ζ (by simpa only [abs_one] using hζ)))
  have hYA : Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 =
      Real.circleAverage (fun ζ => a - Y ζ) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    exact abs_of_nonneg (sub_nonneg.mpr (hYupper ζ (by simpa only [abs_one] using hζ)))
  rw [hXA, hYA,
    Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) hX,
    Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) hY,
    Real.circleAverage_const, hmean]
  ring

theorem circleAverage_abs_diff_zero_of_lower
    (X Y : ℂ → ℝ) (a : ℝ)
    (hX : CircleIntegrable X 0 1) (hY : CircleIntegrable Y 0 1)
    (hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1)
    (hXlower : ∀ ζ ∈ sphere (0 : ℂ) 1, a ≤ X ζ)
    (hYlower : ∀ ζ ∈ sphere (0 : ℂ) 1, a ≤ Y ζ) :
    Real.circleAverage (fun ζ => |a - X ζ|) 0 1 -
      Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 = 0 := by
  have hXA : Real.circleAverage (fun ζ => |a - X ζ|) 0 1 =
      Real.circleAverage (fun ζ => X ζ - a) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    simpa only [neg_sub] using
      (abs_of_nonpos (sub_nonpos.mpr (hXlower ζ (by simpa only [abs_one] using hζ))))
  have hYA : Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 =
      Real.circleAverage (fun ζ => Y ζ - a) 0 1 := by
    apply Real.circleAverage_congr_sphere
    intro ζ hζ
    simpa only [neg_sub] using
      (abs_of_nonpos (sub_nonpos.mpr (hYlower ζ (by simpa only [abs_one] using hζ))))
  rw [hXA, hYA,
    Real.circleAverage_fun_sub hX (circleIntegrable_const _ _ _),
    Real.circleAverage_fun_sub hY (circleIntegrable_const _ _ _),
    Real.circleAverage_const, hmean]
  ring

/-- The actual projected boundary and the line-segment comparator are
circle-integrable. -/
theorem regularExterior_projection_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ξ : ℂ) :
    CircleIntegrable
      (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re) 0 1 := by
  change IntervalIntegrable
    (fun θ : ℝ => (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re)
    volume 0 (2 * Real.pi)
  exact (Complex.continuous_re.comp
    (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)).intervalIntegrable _ _

theorem comparisonCircle_projection_circleIntegrable :
    CircleIntegrable (fun ζ : ℂ => 2 * ζ.re) 0 1 := by
  change IntervalIntegrable (fun θ : ℝ => 2 * (circleMap 0 1 θ).re)
    volume 0 (2 * Real.pi)
  exact (by fun_prop : Continuous (fun θ : ℝ => 2 * (circleMap 0 1 θ).re)).intervalIntegrable _ _

/-- The Round17 vertical-line integral vanishes above both projected
boundary ranges. -/
theorem regularExteriorVerticalPotentialDifference_integral_zero_of_upper
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hXupper : ∀ ζ ∈ sphere (0 : ℂ) 1,
      (conj ξ * rescaleExterior s F ζ).re ≤ a)
    (hYupper : ∀ ζ ∈ sphere (0 : ℂ) 1, 2 * ζ.re ≤ a) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) = 0 := by
  rw [regularExteriorVerticalPotentialDifference_integral F hc hs0 hs1 ξ a]
  have hmean : Real.circleAverage
      (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re) 0 1 =
      Real.circleAverage (fun ζ : ℂ => 2 * ζ.re) 0 1 := by
    rw [rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ,
      comparisonCircle_projection_circleAverage_zero (by norm_num)]
  rw [circleAverage_abs_diff_zero_of_upper _ _ a
    (regularExterior_projection_circleIntegrable F hc hs0 hs1 ξ)
    comparisonCircle_projection_circleIntegrable hmean hXupper hYupper]
  ring

theorem regularExteriorVerticalPotentialDifference_integral_zero_of_lower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hXlower : ∀ ζ ∈ sphere (0 : ℂ) 1,
      a ≤ (conj ξ * rescaleExterior s F ζ).re)
    (hYlower : ∀ ζ ∈ sphere (0 : ℂ) 1, a ≤ 2 * ζ.re) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) = 0 := by
  rw [regularExteriorVerticalPotentialDifference_integral F hc hs0 hs1 ξ a]
  have hmean : Real.circleAverage
      (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re) 0 1 =
      Real.circleAverage (fun ζ : ℂ => 2 * ζ.re) 0 1 := by
    rw [rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ,
      comparisonCircle_projection_circleAverage_zero (by norm_num)]
  rw [circleAverage_abs_diff_zero_of_lower _ _ a
    (regularExterior_projection_circleIntegrable F hc hs0 hs1 ξ)
    comparisonCircle_projection_circleIntegrable hmean hXlower hYlower]
  ring

end SpringerLean
