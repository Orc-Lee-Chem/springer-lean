import SpringerLean.Round27RotatedSubmean

open MeasureTheory Set Metric

namespace SpringerLean

/-- Angular parametrization of a circle average at an arbitrary center. -/
theorem circleAverage_eq_angle_Ioc_general (g : ℂ → ℝ) (c : ℂ) (ρ : ℝ) :
    Real.circleAverage g c ρ =
      (2 * Real.pi)⁻¹ *
        ∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), g (circleMap c ρ θ) := by
  rw [Real.circleAverage_def,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
  rfl

/-- Two normalized circle averages commute for a jointly continuous
real-valued kernel. This is the compact-product Fubini interface needed for
the comparison segment away from its logarithmic pole. -/
theorem circleAverage_circleAverage_comm_of_continuous
    (f : ℂ → ℂ → ℝ)
    (hf : Continuous (fun p : ℂ × ℂ => f p.1 p.2))
    (c : ℂ) (ρ : ℝ) :
    Real.circleAverage
      (fun u : ℂ => Real.circleAverage (fun ζ : ℂ => f u ζ) 0 1) c ρ =
      Real.circleAverage
        (fun ζ : ℂ => Real.circleAverage (fun u : ℂ => f u ζ) c ρ) 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let K : ℝ × ℝ → ℝ := fun p =>
    f (circleMap c ρ p.1) (circleMap 0 1 p.2)
  have hKcont : Continuous K := by
    dsimp [K]
    fun_prop
  have hKint : Integrable K (μ.prod μ) := by
    change Integrable K ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
    rw [Measure.prod_restrict]
    have hcompact : IsCompact
        ((Icc (0 : ℝ) (2 * Real.pi)) ×ˢ (Icc (0 : ℝ) (2 * Real.pi))) :=
      isCompact_Icc.prod isCompact_Icc
    have h := hKcont.continuousOn.integrableOn_compact
      (μ := volume.prod volume) hcompact
    exact h.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap := integral_integral_swap
    (f := fun θ φ : ℝ => K (θ, φ)) (μ := μ) (ν := μ) hKint
  rw [circleAverage_eq_angle_Ioc_general,
    circleAverage_eq_angle_Ioc_general]
  simp_rw [circleAverage_eq_angle_Ioc_general]
  simp only [μ] at hswap
  rw [integral_const_mul, integral_const_mul]
  ring_nf at hswap ⊢
  rw [hswap]

end SpringerLean
