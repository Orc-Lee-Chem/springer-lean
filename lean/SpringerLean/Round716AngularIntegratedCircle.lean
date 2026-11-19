import SpringerLean.Round715AngularHarmonicSwap

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- Genuine circle integrability of the actual angular set integral.
The parameterized kernel is continuous because the whole observation
circle lies in the left half-plane, regardless of the angular source. -/
theorem positiveLogActualProjection_setIntegral_circleIntegrable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (x ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρx : ρ < -x) :
    CircleIntegrable
      (fun z : ℂ => ∫ t in E,
        positiveLogActualProjection F c (z+(t : ℂ)*Complex.I)) (x : ℂ) ρ := by
  let μ : Measure ℝ := volume.restrict E
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2*Real.pi))
  let K : ℝ × ℝ → ℝ := fun p => positiveLogActualProjection F c
    (circleMap (x : ℂ) ρ p.2+(p.1 : ℂ)*Complex.I)
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
    exact (hKcont.continuousOn.integrableOn_compact
      (μ := volume.prod volume) (hEb.isCompact_closure.prod isCompact_Icc)).mono_set
      (Set.prod_mono subset_closure Ioc_subset_Icc_self)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ 2*Real.pi)).mpr
  exact hKint.integral_prod_right

end SpringerLean

#print axioms SpringerLean.positiveLogActualProjection_setIntegral_circleIntegrable
