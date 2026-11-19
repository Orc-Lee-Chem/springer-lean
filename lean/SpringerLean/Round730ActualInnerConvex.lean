import SpringerLean.Round729ActualInnerPositivePart
import SpringerLean.Round644FullConvexCircle

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Complete finite-real convex order on each actual inner circle. -/
theorem actualHarmonic_inner_convex_unitParam_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ univ ψ) :
    Real.circleAverage (fun ζ => ψ ((c*actualHarmonic F ((r : ℂ)*ζ)).re)) 0 1 ≤
      Real.circleAverage (fun ζ : ℂ => ψ (2*r*ζ.re)) 0 1 := by
  let X : ℂ → ℝ := fun ζ => (c*actualHarmonic F ((r : ℂ)*ζ)).re
  let Y : ℂ → ℝ := fun ζ => 2*r*ζ.re
  have harg {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) : ‖(r : ℂ)*ζ‖ = r := by
    have hn : ‖ζ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hζ
    rw [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hscaled : ContinuousOn (fun ζ => actualHarmonic F ((r : ℂ)*ζ)) (sphere (0 : ℂ) 1) := by
    apply (actualHarmonic_continuousOn_unitBall F hc).comp (by fun_prop)
    intro ζ hζ
    rw [mem_ball, dist_zero_right, harg hζ]
    exact hr1
  have hX : ContinuousOn X (sphere (0 : ℂ) 1) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hscaled)
  have hY : ContinuousOn Y (sphere (0 : ℂ) 1) := by dsimp [Y]; fun_prop
  have hXrange : ∀ ζ ∈ sphere (0 : ℂ) 1, X ζ ∈ Icc (-2) 2 := by
    intro ζ hζ
    have hn : ‖(r : ℂ)*ζ‖ < 1 := by rw [harg hζ]; exact hr1
    have hb : |X ζ| ≤ 2 := by
      calc
        _ ≤ ‖c*actualHarmonic F ((r : ℂ)*ζ)‖ := Complex.abs_re_le_norm _
        _ = ‖actualHarmonic F ((r : ℂ)*ζ)‖ := by rw [norm_mul, hcn, one_mul]
        _ ≤ 2*‖(r : ℂ)*ζ‖ := actualHarmonic_norm_le_two_norm F hc hn
        _ ≤ 2 := by rw [harg hζ]; linarith
    exact abs_le.mp hb
  have hYrange : ∀ ζ ∈ sphere (0 : ℂ) 1, Y ζ ∈ Icc (-2) 2 := by
    intro ζ hζ
    have hζn : ‖ζ‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hζ
    have hb : |Y ζ| ≤ 2 := by
      calc
        |Y ζ| = (2*r)*|ζ.re| := by dsimp [Y]; rw [abs_mul, abs_of_nonneg (by positivity)]
        _ ≤ (2*r)*‖ζ‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm ζ) (by positivity)
        _ ≤ 2 := by rw [hζn, mul_one]; linarith
    exact abs_le.mp hb
  have hXmean : Real.circleAverage X 0 1 = 0 := by
    change Real.circleAverage (fun ζ => (c*actualHarmonic F ((r : ℂ)*ζ)).re) 0 1 = 0
    rw [circleAverage_mul_radius_zero (fun z => (c*actualHarmonic F z).re) r]
    simpa only [Complex.conj_conj] using
      actualHarmonic_projection_circleAverage_zero F hc (conj c) hr0 hr1
  have hYmean : Real.circleAverage Y 0 1 = 0 := by
    have heq : Y = fun ζ : ℂ => (fun z : ℂ => 2*z.re) ((r : ℂ)*ζ) := by
      funext ζ
      simp [Y, Complex.mul_re]
      ring
    rw [heq, circleAverage_mul_radius_zero (fun z : ℂ => 2*z.re) r]
    exact comparisonCircle_projection_circleAverage_zero hr0
  exact circleAverage_convex_le_of_positivePart X Y hX hY (a := -2) (b := 2)
    (by norm_num) hXrange hYrange (hXmean.trans hYmean.symm)
    (fun a => actualHarmonic_inner_positivePart_le F hc c hcn hr0 hr1 a) ψ hψ

/-- The paper's actual inner-circle convex order with comparator 2r cos. -/
theorem actualHarmonic_inner_convex_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ univ ψ) :
    Real.circleAverage (fun z => ψ ((conj ξ*actualHarmonic F z).re)) 0 r ≤
      Real.circleAverage (fun z : ℂ => ψ (2*z.re)) 0 r := by
  have hb := actualHarmonic_inner_convex_unitParam_le F hc (conj ξ)
    (by simpa using hξ) hr0 hr1 ψ hψ
  have heq : (fun ζ : ℂ => ψ (2*r*ζ.re)) =
      fun ζ : ℂ => (fun z : ℂ => ψ (2*z.re)) ((r : ℂ)*ζ) := by
    funext ζ
    congr 1
    simp [Complex.mul_re]
    ring
  rw [heq, circleAverage_mul_radius_zero (fun z => ψ (2*z.re)) r,
    circleAverage_mul_radius_zero (fun z => ψ ((conj ξ*actualHarmonic F z).re)) r] at hb
  exact hb

end SpringerLean

#print axioms SpringerLean.actualHarmonic_inner_convex_unitParam_le
#print axioms SpringerLean.actualHarmonic_inner_convex_le
