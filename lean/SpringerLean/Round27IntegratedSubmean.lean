import SpringerLean.Round27GlobalRotatedSubmean

open MeasureTheory Set Metric

namespace SpringerLean

/-- Integrate a pointwise circle-submean inequality over a bounded measurable
vertical set. Product integrability makes the monotonicity and Fubini steps
valid even for a merely measurable kernel. -/
theorem setIntegral_le_circleAverage_setIntegral_of_pointwise_submean
    (f : ℝ → ℂ → ℝ)
    (hf : Measurable (fun p : ℝ × ℂ => f p.1 p.2))
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ C : ℝ)
    (hC : ∀ t ∈ E, ∀ z ∈ sphere c |ρ|, ‖f t z‖ ≤ C)
    (hcenter : IntegrableOn (fun t => f t c) E)
    (hsub : ∀ t ∈ E, f t c ≤ Real.circleAverage (f t) c ρ) :
    (∫ t in E, f t c) ≤
      Real.circleAverage (fun z => ∫ t in E, f t z) c ρ := by
  let μ : Measure ℝ := volume.restrict E
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  have hKint : Integrable
      (fun p : ℝ × ℝ => f p.1 (circleMap c ρ p.2)) (μ.prod ν) :=
    bounded_measurable_circle_kernel_integrable f hf E hEm hEb c ρ C hC
  have hright : IntegrableOn
      (fun t => Real.circleAverage (f t) c ρ) E := by
    have hint := hKint.integral_prod_left
    change Integrable (fun t => Real.circleAverage (f t) c ρ) μ
    have heq : (fun t => Real.circleAverage (f t) c ρ) =
        (fun t => (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ, f t (circleMap c ρ θ) ∂ν) := by
      funext t
      rw [circleAverage_eq_angle_Ioc_general]
    rw [heq]
    exact hint.const_mul _
  have hmono := setIntegral_mono_on hcenter hright hEm hsub
  rw [setIntegral_circleAverage_swap_of_measurable_bounded
    f hf E hEm hEb c ρ C hC] at hmono
  exact hmono

end SpringerLean