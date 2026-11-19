import SpringerLean.Round15Derivative
import SpringerLean.Round14BoundaryMean

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The algebraic bridge from an absolute-deviation comparison to positive
part tests, when the two normalized circle variables have equal means. -/
theorem circleAverage_abs_difference_eq_two_posPart_difference
    (X Y : ℂ → ℝ)
    (hX : ContinuousOn X (sphere (0 : ℂ) 1))
    (hY : ContinuousOn Y (sphere (0 : ℂ) 1))
    (hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1)
    (a : ℝ) :
    Real.circleAverage (fun z => |X z - a|) 0 1 -
      Real.circleAverage (fun z => |Y z - a|) 0 1 =
      2 * (Real.circleAverage (fun z => max (X z - a) 0) 0 1 -
        Real.circleAverage (fun z => max (Y z - a) 0) 0 1) := by
  have hpoint (x : ℝ) : |x - a| = 2 * max (x - a) 0 - (x - a) := by
    by_cases hx : 0 ≤ x - a
    · rw [abs_of_nonneg hx, max_eq_left hx]
      ring
    · have hle : x - a ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hle, max_eq_right hle]
      ring
  have hcalc (Z : ℂ → ℝ) (hZ : ContinuousOn Z (sphere (0 : ℂ) 1)) :
      Real.circleAverage (fun z => |Z z - a|) 0 1 =
        2 * Real.circleAverage (fun z => max (Z z - a) 0) 0 1 -
          Real.circleAverage Z 0 1 + a := by
    have hP : ContinuousOn (fun z => max (Z z - a) 0) (sphere (0 : ℂ) 1) := by
      fun_prop
    have hPa : CircleIntegrable (fun z => max (Z z - a) 0) 0 1 :=
      hP.circleIntegrable (by norm_num)
    have hZa : CircleIntegrable (fun z => Z z - a) 0 1 :=
      (by fun_prop : ContinuousOn (fun z => Z z - a) (sphere (0 : ℂ) 1)).circleIntegrable
        (by norm_num)
    have hZi : CircleIntegrable Z 0 1 := hZ.circleIntegrable (by norm_num)
    calc
      _ = Real.circleAverage
          (fun z => 2 * max (Z z - a) 0 - (Z z - a)) 0 1 := by
        apply Real.circleAverage_congr_sphere
        intro z _
        exact hpoint (Z z)
      _ = Real.circleAverage (fun z => 2 * max (Z z - a) 0) 0 1 -
          Real.circleAverage (fun z => Z z - a) 0 1 := by
        exact Real.circleAverage_fun_sub (hPa.const_mul 2) hZa
      _ = 2 * Real.circleAverage (fun z => max (Z z - a) 0) 0 1 -
          (Real.circleAverage Z 0 1 - a) := by
        rw [show Real.circleAverage (fun z => 2 * max (Z z - a) 0) 0 1 =
          2 * Real.circleAverage (fun z => max (Z z - a) 0) 0 1 by
            simpa only [smul_eq_mul] using
              (Real.circleAverage_fun_smul (a := (2 : ℝ))
                (f := fun z => max (Z z - a) 0) (c := (0 : ℂ)) (R := 1))]
        rw [Real.circleAverage_fun_sub hZi (circleIntegrable_const _ _ _),
          Real.circleAverage_const]
      _ = _ := by ring
  rw [hcalc X hX, hcalc Y hY, hmean]
  ring

/-- For the actual regularized exterior boundary and the comparison
circle, the absolute-deviation difference is twice the positive-part
difference. The two variables use the same normalized angle measure. -/
theorem regularExterior_projection_abs_diff_eq_two_posPart_diff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    Real.circleAverage
        (fun ζ => |(conj ξ * rescaleExterior s F ζ).re - a|) 0 1 -
      Real.circleAverage (fun ζ : ℂ => |2 * ζ.re - a|) 0 1 =
      2 * (Real.circleAverage
          (fun ζ => max ((conj ξ * rescaleExterior s F ζ).re - a) 0) 0 1 -
        Real.circleAverage (fun ζ : ℂ => max (2 * ζ.re - a) 0) 0 1) := by
  let X : ℂ → ℝ := fun ζ => (conj ξ * rescaleExterior s F ζ).re
  let Y : ℂ → ℝ := fun ζ => 2 * ζ.re
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hX : ContinuousOn X (sphere (0 : ℂ) 1) := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = 1 := by
      simpa [mem_sphere, dist_zero_right] using hζ
    have hext : ζ ∈ exteriorAbove s := by
      change s < ‖ζ‖
      rw [hnorm]
      exact hs1
    have hGa := (rescaleExterior_analyticAt hs0 hF hext).continuousAt
    have hprod : ContinuousAt (fun y : ℂ => conj ξ * rescaleExterior s F y) ζ :=
      continuousAt_const.mul hGa
    exact (Complex.continuous_re.continuousAt.comp hprod).continuousWithinAt
  have hY : ContinuousOn Y (sphere (0 : ℂ) 1) := by
    fun_prop
  have hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1 := by
    rw [show Real.circleAverage X 0 1 = 0 from
      rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ]
    exact (comparisonCircle_projection_circleAverage_zero (by norm_num)).symm
  exact circleAverage_abs_difference_eq_two_posPart_difference X Y hX hY hmean a

end SpringerLean
