import SpringerLean.Round1893LocalConvexCircle
import SpringerLean.Round32SignApplications
import SpringerLean.Round639RegularBoundaryOmitted

open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false

/-- Complete finite-real convex comparison on the actual smooth boundary.
The comparator is the unit-circle variable 2 Re ζ, not the disk semicircle
law and not the still-separate inner-circle comparator 2r cos θ. -/
theorem regularExterior_localConvex_boundary_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ (Set.Icc (-2) 2) ψ)
    (hψc : Continuous ψ) :
    Real.circleAverage
      (fun ζ => ψ ((conj ξ*rescaleExterior s F ζ).re)) 0 1 ≤
    Real.circleAverage (fun ζ : ℂ => ψ (2*ζ.re)) 0 1 := by
  let X : ℂ → ℝ := fun ζ => (conj ξ*rescaleExterior s F ζ).re
  let Y : ℂ → ℝ := fun ζ => 2*ζ.re
  have hX := regularExterior_projection_continuousOn_sphere F hc hs0 hs1 ξ
  have hY : ContinuousOn Y (Metric.sphere (0 : ℂ) 1) := by fun_prop
  have hXrange : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, X ζ ∈ Set.Icc (-2) 2 := by
    intro ζ hζ
    have hζn : ‖ζ‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hζ
    have hK := rescaleExterior_unitCircle_mem_omitted F hc hs0 hs1 hζn
    have hnorm := exteriorOmitted_norm_le_two _
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1) hK
    have hbound : |X ζ| ≤ 2 := by
      calc
        _ ≤ ‖conj ξ*rescaleExterior s F ζ‖ := Complex.abs_re_le_norm _
        _ = ‖rescaleExterior s F ζ‖ := by rw [norm_mul,Complex.norm_conj,hξ,one_mul]
        _ ≤ 2 := hnorm
    exact abs_le.mp hbound
  have hYrange : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, Y ζ ∈ Set.Icc (-2) 2 := by
    intro ζ hζ
    have hζn : ‖ζ‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hζ
    have hbound : |Y ζ| ≤ 2 := by
      dsimp only [Y]
      calc
        |2*ζ.re| = 2*|ζ.re| := by simp
        _ ≤ 2*‖ζ‖ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm ζ) (by norm_num)
        _ = 2 := by rw [hζn,mul_one]
    exact abs_le.mp hbound
  have hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1 := by
    rw [rescaleExterior_projected_boundary_circleAverage_zero F hc hs0 hs1 ξ,
      comparisonCircle_projection_circleAverage_zero (by norm_num)]
  exact circleAverage_convex_le_of_positivePart_local X Y hX hY
    (a := -2) (b := 2) (by norm_num) hXrange hYrange hmean
    (fun c => regularExterior_positivePart_le F hc hs0 hs1 ξ hξ c) ψ hψ hψc

end SpringerLean
