import SpringerLean.Round27VerticalCircleSwap

open MeasureTheory Set Metric
open scoped ENNReal

namespace SpringerLean

/-- A measurable bounded kernel can be integrated first over a bounded real
set and then over a circle, or in the reverse order. This does not require
continuity at a logarithmic boundary. -/
theorem setIntegral_circleAverage_swap_of_measurable_bounded
    (f : ℝ → ℂ → ℝ)
    (hf : Measurable (fun p : ℝ × ℂ => f p.1 p.2))
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ : ℝ)
    (C : ℝ) (hC : ∀ t ∈ E, ∀ z ∈ sphere c |ρ|, ‖f t z‖ ≤ C) :
    (∫ t in E, Real.circleAverage (f t) c ρ) =
      Real.circleAverage (fun z => ∫ t in E, f t z) c ρ := by
  let μ : Measure ℝ := volume.restrict E
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let K : ℝ × ℝ → ℝ := fun p => f p.1 (circleMap c ρ p.2)
  have hKmeas : Measurable K := by
    dsimp [K]
    have hp : Measurable (fun p : ℝ × ℝ => (p.1, circleMap c ρ p.2)) := by fun_prop
    exact hf.comp hp
  have hKint : Integrable K (μ.prod ν) := by
    change Integrable K ((volume.restrict E).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    rw [Measure.prod_restrict]
    have hS : MeasurableSet (E ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) :=
      hEm.prod measurableSet_Ioc
    have hfinite : (volume.prod volume) (E ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) < ∞ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_lt_top hEb.measure_lt_top measure_Ioc_lt_top
    apply IntegrableOn.of_bound hfinite hKmeas.aestronglyMeasurable C
    apply (ae_restrict_iff' hS).2
    filter_upwards [] with p hp
    exact hC p.1 hp.1 (circleMap c ρ p.2)
      (circleMap_mem_sphere' c ρ p.2)
  have hswap := integral_integral_swap
    (f := fun t θ : ℝ => K (t, θ)) (μ := μ) (ν := ν) hKint
  simp only [μ, ν] at hswap
  rw [circleAverage_eq_angle_Ioc_general]
  simp_rw [circleAverage_eq_angle_Ioc_general]
  rw [integral_const_mul]
  ring_nf at hswap ⊢
  rw [hswap]


/-- The product-integrability fact underlying the measurable circle swap,
exported separately for monotone integration over vertical sets. -/
theorem bounded_measurable_circle_kernel_integrable
    (f : ℝ → ℂ → ℝ)
    (hf : Measurable (fun p : ℝ × ℂ => f p.1 p.2))
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ C : ℝ)
    (hC : ∀ t ∈ E, ∀ z ∈ sphere c |ρ|, ‖f t z‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => f p.1 (circleMap c ρ p.2))
      ((volume.restrict E).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  have hKmeas : Measurable (fun p : ℝ × ℝ => f p.1 (circleMap c ρ p.2)) := by
    have hp : Measurable (fun p : ℝ × ℝ => (p.1, circleMap c ρ p.2)) := by fun_prop
    exact hf.comp hp
  rw [Measure.prod_restrict]
  have hS : MeasurableSet (E ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) :=
    hEm.prod measurableSet_Ioc
  have hfinite : (volume.prod volume) (E ×ˢ Ioc (0 : ℝ) (2 * Real.pi)) < ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top hEb.measure_lt_top measure_Ioc_lt_top
  apply IntegrableOn.of_bound hfinite hKmeas.aestronglyMeasurable C
  apply (ae_restrict_iff' hS).2
  filter_upwards [] with p hp
  exact hC p.1 hp.1 (circleMap c ρ p.2)
    (circleMap_mem_sphere' c ρ p.2)
end SpringerLean