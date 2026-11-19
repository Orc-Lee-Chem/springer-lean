import SpringerLean.Round27ComparisonMean

open MeasureTheory Set Metric

namespace SpringerLean

/-- Swap a circle average with integration over a bounded measurable real set
for a jointly continuous kernel. This gives an honest product-integrability
interface for the vertical cost problem. -/
theorem setIntegral_circleAverage_swap_of_continuous
    (f : ℝ → ℂ → ℝ)
    (hf : Continuous (fun p : ℝ × ℂ => f p.1 p.2))
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c : ℂ) (ρ : ℝ) :
    (∫ t in E, Real.circleAverage (f t) c ρ) =
      Real.circleAverage (fun z => ∫ t in E, f t z) c ρ := by
  let μ : Measure ℝ := volume.restrict E
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let K : ℝ × ℝ → ℝ := fun p => f p.1 (circleMap c ρ p.2)
  have hKcont : Continuous K := by
    dsimp [K]
    fun_prop
  have hKint : Integrable K (μ.prod ν) := by
    change Integrable K ((volume.restrict E).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    rw [Measure.prod_restrict]
    have hcompact : IsCompact ((closure E) ×ˢ (Icc (0 : ℝ) (2 * Real.pi))) :=
      hEb.isCompact_closure.prod isCompact_Icc
    have h := hKcont.continuousOn.integrableOn_compact
      (μ := volume.prod volume) hcompact
    apply h.mono_set
    exact Set.prod_mono subset_closure Ioc_subset_Icc_self
  have hswap := integral_integral_swap
    (f := fun t θ : ℝ => K (t, θ)) (μ := μ) (ν := ν) hKint
  simp only [μ, ν] at hswap
  rw [circleAverage_eq_angle_Ioc_general]
  simp_rw [circleAverage_eq_angle_Ioc_general]
  rw [integral_const_mul]
  ring_nf at hswap ⊢
  rw [hswap]

end SpringerLean
