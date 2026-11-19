import SpringerLean.Round30ActualCenterComplement
import SpringerLean.Round27VerticalCircleSwapMeasurable

open MeasureTheory Set Metric

namespace SpringerLean

/-- A bounded measurable vertical-set integral of a jointly measurable kernel
that is uniformly bounded on the target circle is itself circle integrable. -/
theorem bounded_measurable_vertical_set_integral_circleIntegrable
    (f : ℝ → ℂ → ℝ)
    (hf : Measurable (fun p : ℝ × ℂ => f p.1 p.2))
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ C : ℝ)
    (hC : ∀ t ∈ E, ∀ z ∈ sphere c |ρ|, ‖f t z‖ ≤ C) :
    CircleIntegrable (fun z : ℂ => ∫ t in E, f t z) c ρ := by
  have hprod := bounded_measurable_circle_kernel_integrable
    f hf E hEm hEb c ρ C hC
  have hangle : Integrable
      (fun θ : ℝ => ∫ t in E, f t (circleMap c ρ θ))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    simpa only using hprod.integral_prod_right
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)).2 hangle


/-- Continuous kernels on a bounded vertical parameter set automatically give
circle-integrable set integrals. -/
theorem continuous_vertical_set_integral_circleIntegrable
    (f : ℝ → ℂ → ℝ)
    (hf : Continuous (fun p : ℝ × ℂ => f p.1 p.2))
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ : ℝ) :
    CircleIntegrable (fun z : ℂ => ∫ t in E, f t z) c ρ := by
  let K : ℝ × ℝ → ℝ := fun p => f p.1 (circleMap c ρ p.2)
  have hKcont : Continuous K := by
    dsimp [K]
    fun_prop
  have hprod : Integrable K
      ((volume.restrict E).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    have hcompact : IsCompact ((closure E) ×ˢ (Icc (0 : ℝ) (2 * Real.pi))) :=
      hEb.isCompact_closure.prod isCompact_Icc
    exact (hKcont.continuousOn.integrableOn_compact
      (μ := volume.prod volume) hcompact).mono_set
        (Set.prod_mono subset_closure Ioc_subset_Icc_self)
  have hangle : Integrable
      (fun θ : ℝ => ∫ t in E, f t (circleMap c ρ θ))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := by
    simpa only using hprod.integral_prod_right
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (show (0 : ℝ) ≤ 2 * Real.pi by positivity)).2 hangle
end SpringerLean