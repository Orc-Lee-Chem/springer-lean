import SpringerLean.Round707PositiveLogMean
import SpringerLean.Round27VerticalCircleSwap

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false

/-- Integrating the SAME actual positive-angle harmonic projection over a
bounded measurable angular set commutes with a local circle average.
Only the left half-plane is used; no global measurability of arbitrary F
outside its prescribed domain is asserted. -/
theorem positiveLogActualProjection_setIntegral_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (x ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρx : ρ < -x) :
    (∫ t in E, positiveLogActualProjection F c ((x : ℂ)+(t : ℂ)*Complex.I)) =
      Real.circleAverage
        (fun z : ℂ => ∫ t in E,
          positiveLogActualProjection F c (z+(t : ℂ)*Complex.I)) (x : ℂ) ρ := by
  let P := positiveLogActualProjection F c
  let μ : Measure ℝ := volume.restrict E
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2*Real.pi))
  let K : ℝ × ℝ → ℝ := fun p => P (circleMap (x : ℂ) ρ p.2+(p.1 : ℂ)*Complex.I)
  have hcircle (θ : ℝ) : (circleMap (x : ℂ) ρ θ).re < 0 := by
    have hn : ‖circleMap (x : ℂ) ρ θ-(x : ℂ)‖ = ρ := by
      simpa only [mem_sphere, dist_eq_norm, abs_of_nonneg hρ0] using
        circleMap_mem_sphere' (x : ℂ) ρ θ
    have hre := Complex.re_le_norm (circleMap (x : ℂ) ρ θ-(x : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, hn] at hre
    linarith
  have hKcont : Continuous K := by
    apply (positiveLogActualProjection_continuousOn F hc c).comp_continuous
      (by fun_prop : Continuous (fun p : ℝ × ℝ =>
        circleMap (x : ℂ) ρ p.2+(p.1 : ℂ)*Complex.I))
    intro p
    change (circleMap (x : ℂ) ρ p.2+(p.1 : ℂ)*Complex.I).re < 0
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero] using hcircle p.2
  have hKint : Integrable K (μ.prod ν) := by
    change Integrable K ((volume.restrict E).prod
      (volume.restrict (Ioc (0 : ℝ) (2*Real.pi))))
    rw [Measure.prod_restrict]
    have hcompact : IsCompact (closure E ×ˢ Icc (0 : ℝ) (2*Real.pi)) :=
      hEb.isCompact_closure.prod isCompact_Icc
    exact (hKcont.continuousOn.integrableOn_compact
      (μ := volume.prod volume) hcompact).mono_set
      (Set.prod_mono subset_closure Ioc_subset_Icc_self)
  have hswap := integral_integral_swap
    (f := fun t θ : ℝ => K (t, θ)) (μ := μ) (ν := ν) hKint
  have hswapMean :
      (∫ t in E, Real.circleAverage
        (fun z : ℂ => P (z+(t : ℂ)*Complex.I)) (x : ℂ) ρ) =
      Real.circleAverage (fun z : ℂ => ∫ t in E, P (z+(t : ℂ)*Complex.I))
        (x : ℂ) ρ := by
    simp only [μ, ν, K] at hswap
    rw [circleAverage_eq_angle_Ioc_general]
    simp_rw [circleAverage_eq_angle_Ioc_general]
    rw [integral_const_mul]
    exact congrArg (fun y : ℝ => (2*Real.pi)⁻¹*y) hswap
  have hmean (t : ℝ) : Real.circleAverage
      (fun z : ℂ => P (z+(t : ℂ)*Complex.I)) (x : ℂ) ρ =
      P ((x : ℂ)+(t : ℂ)*Complex.I) := by
    have htranslate : Real.circleAverage
        (fun z : ℂ => P (z+(t : ℂ)*Complex.I)) (x : ℂ) ρ =
        Real.circleAverage P ((x : ℂ)+(t : ℂ)*Complex.I) ρ := by
      rw [Real.circleAverage_def, Real.circleAverage_def]
      congr 1
      apply intervalIntegral.integral_congr
      intro θ hθ
      apply congrArg P
      simp only [circleMap]
      ring
    rw [htranslate]
    exact positiveLogActualProjection_circleAverage F hc c hρ0
      (by simpa using hρx)
  simpa only [hmean] using hswapMean

end SpringerLean

#print axioms SpringerLean.positiveLogActualProjection_setIntegral_circleAverage
