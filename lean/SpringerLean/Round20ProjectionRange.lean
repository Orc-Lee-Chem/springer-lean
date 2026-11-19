import SpringerLean.Round18Tail

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- A centered projected variable supported to the left of `a` has no
larger absolute-deviation average than any other centered variable. -/
theorem circleAverage_abs_diff_le_of_upper
    (X Y : ℂ → ℝ) (a : ℝ)
    (hX : CircleIntegrable X 0 1) (hY : CircleIntegrable Y 0 1)
    (hXzero : Real.circleAverage X 0 1 = 0)
    (hYzero : Real.circleAverage Y 0 1 = 0)
    (hXupper : ∀ ζ ∈ sphere (0 : ℂ) 1, X ζ ≤ a) :
    Real.circleAverage (fun ζ => |a - X ζ|) 0 1 -
      Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 ≤ 0 := by
  have hleft : Real.circleAverage (fun ζ => |a - X ζ|) 0 1 = a := by
    calc
      _ = Real.circleAverage (fun ζ => a - X ζ) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro ζ hζ
        exact abs_of_nonneg (sub_nonneg.mpr
          (hXupper ζ (by simpa only [abs_one] using hζ)))
      _ = a := by
        rw [Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) hX,
          Real.circleAverage_const, hXzero]
        ring
  have hmean : Real.circleAverage (fun ζ => a - Y ζ) 0 1 = a := by
    rw [Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) hY,
      Real.circleAverage_const, hYzero]
    ring
  have hright := Real.abs_circleAverage_le_circleAverage_abs
    (c := (0 : ℂ)) (R := (1 : ℝ)) (f := fun ζ => a - Y ζ)
  rw [hmean] at hright
  change |a| ≤ Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 at hright
  rw [hleft]
  linarith [le_abs_self a]

/-- The corresponding lower-range statement, including the endpoint. -/
theorem circleAverage_abs_diff_le_of_lower
    (X Y : ℂ → ℝ) (a : ℝ)
    (hX : CircleIntegrable X 0 1) (hY : CircleIntegrable Y 0 1)
    (hXzero : Real.circleAverage X 0 1 = 0)
    (hYzero : Real.circleAverage Y 0 1 = 0)
    (hXlower : ∀ ζ ∈ sphere (0 : ℂ) 1, a ≤ X ζ) :
    Real.circleAverage (fun ζ => |a - X ζ|) 0 1 -
      Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 ≤ 0 := by
  have hleft : Real.circleAverage (fun ζ => |a - X ζ|) 0 1 = -a := by
    calc
      _ = Real.circleAverage (fun ζ => X ζ - a) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro ζ hζ
        simpa only [neg_sub] using (abs_of_nonpos
          (sub_nonpos.mpr (hXlower ζ (by simpa only [abs_one] using hζ))))
      _ = -a := by
        rw [Real.circleAverage_fun_sub hX (circleIntegrable_const _ _ _),
          Real.circleAverage_const, hXzero]
        ring
  have hmean : Real.circleAverage (fun ζ => a - Y ζ) 0 1 = a := by
    rw [Real.circleAverage_fun_sub (circleIntegrable_const _ _ _) hY,
      Real.circleAverage_const, hYzero]
    ring
  have hright := Real.abs_circleAverage_le_circleAverage_abs
    (c := (0 : ℂ)) (R := (1 : ℝ)) (f := fun ζ => a - Y ζ)
  rw [hmean] at hright
  change |a| ≤ Real.circleAverage (fun ζ => |a - Y ζ|) 0 1 at hright
  rw [hleft]
  linarith [neg_le_abs a]

/-- Unconditional actual vertical sign above the entire projected smooth
boundary. The comparator may still have points farther to the right. -/
theorem regularExteriorVerticalPotentialDifference_integral_le_zero_of_upper
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hXupper : ∀ ζ ∈ sphere (0 : ℂ) 1,
      (conj ξ * rescaleExterior s F ζ).re ≤ a) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0 := by
  rw [regularExteriorVerticalPotentialDifference_integral F hc hs0 hs1 ξ a]
  have h := circleAverage_abs_diff_le_of_upper
    (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re)
    (fun ζ : ℂ => 2 * ζ.re) a
    (regularExterior_projection_circleIntegrable F hc hs0 hs1 ξ)
    comparisonCircle_projection_circleIntegrable
    (rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ)
    (comparisonCircle_projection_circleAverage_zero (by norm_num)) hXupper
  exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h

/-- Unconditional actual vertical sign below the entire projected smooth
boundary. No comparator-side range condition is imposed. -/
theorem regularExteriorVerticalPotentialDifference_integral_le_zero_of_lower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ)
    (hXlower : ∀ ζ ∈ sphere (0 : ℂ) 1,
      a ≤ (conj ξ * rescaleExterior s F ζ).re) :
    (∫ y : ℝ, regularExteriorVerticalPotentialDifference F s ξ a y) ≤ 0 := by
  rw [regularExteriorVerticalPotentialDifference_integral F hc hs0 hs1 ξ a]
  have h := circleAverage_abs_diff_le_of_lower
    (fun ζ : ℂ => (conj ξ * rescaleExterior s F ζ).re)
    (fun ζ : ℂ => 2 * ζ.re) a
    (regularExterior_projection_circleIntegrable F hc hs0 hs1 ξ)
    comparisonCircle_projection_circleIntegrable
    (rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ)
    (comparisonCircle_projection_circleAverage_zero (by norm_num)) hXlower
  exact mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h

end SpringerLean
