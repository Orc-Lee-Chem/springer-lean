import SpringerLean.Round17ActualRaw

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- Actual-minus-comparison potential difference on a vertical line.
Each circle average uses the same probability angle measure. -/
noncomputable def regularExteriorVerticalPotentialDifference
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a y : ℝ) : ℝ :=
  Real.circleAverage
    (fun ζ : ℂ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) -
      conj ξ * rescaleExterior s F ζ‖) 0 1 -
  Real.circleAverage
    (fun ζ : ℂ => Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I) -
      ((2 * ζ.re : ℝ) : ℂ)‖) 0 1

/-- Raw circle-average potentials equal their compensated counterparts
for every vertical coordinate, including curve crossings. -/
theorem regularExteriorVerticalPotentialDifference_eq_compensated
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a y : ℝ) :
    regularExteriorVerticalPotentialDifference F s ξ a y =
      (2 * Real.pi)⁻¹ *
        ((∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          verticalPointKernel a
            (conj ξ * rescaleExterior s F (circleMap 0 1 θ)) y) -
         (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi),
          verticalPointKernel a
            ((2 * (circleMap 0 1 θ).re : ℝ) : ℂ) y)) := by
  rw [regularExteriorVerticalPotentialDifference,
    circleAverage_eq_angle_Ioc, circleAverage_eq_angle_Ioc]
  rw [← mul_sub]
  exact congrArg ((2 * Real.pi)⁻¹ * ·)
    (regularExterior_compensated_eq_raw_angle F hc hs0 hs1 ξ a y).symm

/-- Round17-A: the actual vertical-line potential difference is L¹,
with no exception for lines through the boundary curve. -/
theorem regularExteriorVerticalPotentialDifference_integrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    Integrable (regularExteriorVerticalPotentialDifference F s ξ a) := by
  have h := (regularExterior_compensated_vertical_integrable
    F hc hs0 hs1 ξ a).const_mul ((2 * Real.pi)⁻¹)
  convert h using 1
  funext y
  exact regularExteriorVerticalPotentialDifference_eq_compensated
    F hc hs0 hs1 ξ a y

/-- Round17-B: the exact vertical-line logarithmic potential identity for
the actual regularized map and the comparison circle. -/
theorem regularExteriorVerticalPotentialDifference_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) =
      Real.pi *
        (Real.circleAverage
          (fun ζ : ℂ => |a - (conj ξ * rescaleExterior s F ζ).re|) 0 1 -
         Real.circleAverage (fun ζ : ℂ => |a - 2 * ζ.re|) 0 1) := by
  simp_rw [regularExteriorVerticalPotentialDifference_eq_compensated
    F hc hs0 hs1 ξ a]
  exact regularExterior_compensated_vertical_circleAverage F hc hs0 hs1 ξ a

/-- The same unconditional identity expressed by the positive-part tests
used in the boundary convex-order problem. -/
theorem regularExteriorVerticalPotentialDifference_integral_posPart
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) =
      2 * Real.pi *
        (Real.circleAverage
          (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 -
         Real.circleAverage
          (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1) := by
  rw [regularExteriorVerticalPotentialDifference_integral F hc hs0 hs1 ξ a]
  have h := regularExterior_projection_abs_diff_eq_two_posPart_diff
    F hc hs0 hs1 ξ a
  have hleft : Real.circleAverage
      (fun ζ : ℂ => |a - (conj ξ * rescaleExterior s F ζ).re|) 0 1 =
      Real.circleAverage
        (fun ζ : ℂ => |(conj ξ * rescaleExterior s F ζ).re - a|) 0 1 := by
    congr 1
    funext ζ
    exact abs_sub_comm _ _
  have hright : Real.circleAverage (fun ζ : ℂ => |a - 2 * ζ.re|) 0 1 =
      Real.circleAverage (fun ζ : ℂ => |2 * ζ.re - a|) 0 1 := by
    congr 1
    funext ζ
    exact abs_sub_comm _ _
  rw [hleft, hright, h]
  ring

end SpringerLean
