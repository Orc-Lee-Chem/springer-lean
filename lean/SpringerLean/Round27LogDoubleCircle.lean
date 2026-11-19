import SpringerLean.Round27LogAbsBound

open MeasureTheory Set Metric
open scoped ENNReal

namespace SpringerLean

/-- Joint integrability of the logarithmic kernel on two circles, even if
the moving boundary curve intersects the outer circle. -/
theorem circle_log_kernel_prod_integrable
    (b : ℂ → ℂ)
    (hb : Continuous (fun θ : ℝ => b (circleMap 0 1 θ)))
    (M : ℝ) (hM : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖b ζ‖ ≤ M)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Integrable
      (fun p : ℝ × ℝ =>
        Real.log ‖circleMap c ρ p.1 - b (circleMap 0 1 p.2)‖)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.log ‖circleMap c ρ p.1 - b (circleMap 0 1 p.2)‖
  have hKmeas : Measurable K := by
    have hbm : Measurable (fun θ : ℝ => b (circleMap 0 1 θ)) := hb.measurable
    have hm1 : Measurable (fun p : ℝ × ℝ => circleMap c ρ p.1) := by fun_prop
    have hm2 : Measurable (fun p : ℝ × ℝ => b (circleMap 0 1 p.2)) :=
      hbm.comp measurable_snd
    exact (hm1.sub hm2).norm.log
  have hsection (θ : ℝ) : Integrable (fun t : ℝ => K (t, θ)) μ := by
    change Integrable (fun t : ℝ =>
      Real.log ‖circleMap c ρ t - b (circleMap 0 1 θ)‖)
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity)).mp
      (circleIntegrable_log_norm_sub_const ρ)
  have hLmeas : AEStronglyMeasurable
      (fun θ : ℝ => ∫ t : ℝ, ‖K (t, θ)‖ ∂μ) μ :=
    hKmeas.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hLbound : ∀ θ : ℝ,
      (∫ t : ℝ, ‖K (t, θ)‖ ∂μ) ≤
        (2 * Real.pi) *
          (2 * (‖c‖ + |ρ| + M + 1) - Real.log ρ) := by
    intro θ
    have hbM : ‖b (circleMap 0 1 θ)‖ ≤ M :=
      hM _ (by simpa using circleMap_mem_sphere' 0 1 θ)
    have habs := log_norm_circleAverage_abs_le c
      (b (circleMap 0 1 θ)) ρ hρ
    rw [circleAverage_eq_angle_Ioc_general] at habs
    have htwopi : 0 < 2 * Real.pi := by positivity
    have hnorm : ∫ t : ℝ, ‖K (t, θ)‖ ∂μ =
        ∫ t in Ioc (0 : ℝ) (2 * Real.pi),
          |Real.log ‖circleMap c ρ t - b (circleMap 0 1 θ)‖| := by
      rfl
    rw [hnorm]
    have h := mul_le_mul_of_nonneg_left habs (le_of_lt htwopi)
    field_simp at h
    nlinarith
  have hLInt : Integrable
      (fun θ : ℝ => ∫ t : ℝ, ‖K (t, θ)‖ ∂μ) μ := by
    haveI : IsFiniteMeasure μ := inferInstance
    apply Integrable.of_bound hLmeas
      ((2 * Real.pi) * (2 * (‖c‖ + |ρ| + M + 1) - Real.log ρ))
    filter_upwards [] with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hLbound θ
  apply (integrable_prod_iff' hKmeas.aestronglyMeasurable).2
  exact ⟨ae_of_all _ hsection, hLInt⟩


/-- Two circle averages of the logarithmic kernel commute even when the
boundary curve meets the second circle. Joint absolute integrability is
proved by the uniform circle bound above. -/
theorem circleAverage_circleAverage_log_swap
    (b : ℂ → ℂ)
    (hb : Continuous (fun θ : ℝ => b (circleMap 0 1 θ)))
    (M : ℝ) (hM : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖b ζ‖ ≤ M)
    (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    Real.circleAverage
      (fun u : ℂ => Real.circleAverage
        (fun ζ : ℂ => Real.log ‖u - b ζ‖) 0 1) c ρ =
      Real.circleAverage
        (fun ζ : ℂ => Real.circleAverage
          (fun u : ℂ => Real.log ‖u - b ζ‖) c ρ) 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.log ‖circleMap c ρ p.1 - b (circleMap 0 1 p.2)‖
  have hKint : Integrable K (μ.prod μ) :=
    circle_log_kernel_prod_integrable b hb M hM c ρ hρ
  have hswap := integral_integral_swap
    (f := fun θ φ : ℝ => K (θ, φ)) (μ := μ) (ν := μ) hKint
  simp only [μ] at hswap
  rw [circleAverage_eq_angle_Ioc_general,
    circleAverage_eq_angle_Ioc_general]
  simp_rw [circleAverage_eq_angle_Ioc_general]
  rw [integral_const_mul, integral_const_mul]
  ring_nf at hswap ⊢
  rw [hswap]

/-- Logarithmic potentials of continuous bounded circle curves have the
circular submean property at centers off the curve. The second circle may
intersect the curve: the singular double integral is handled by the
preceding absolute-integrability theorem. -/
theorem boundary_log_potential_circle_submean_of_not_mem_curve
    (b : ℂ → ℂ)
    (hb : ContinuousOn b (sphere (0 : ℂ) 1))
    (M : ℝ) (hM : ∀ ζ ∈ sphere (0 : ℂ) 1, ‖b ζ‖ ≤ M)
    (c : ℂ) (hc : c ∉ b '' sphere (0 : ℂ) 1)
    (ρ : ℝ) (hρ : 0 < ρ) :
    Real.circleAverage (fun ζ : ℂ => Real.log ‖c - b ζ‖) 0 1 ≤
      Real.circleAverage
        (fun u : ℂ => Real.circleAverage
          (fun ζ : ℂ => Real.log ‖u - b ζ‖) 0 1) c ρ := by
  have hangle : Continuous (fun θ : ℝ => b (circleMap 0 1 θ)) := by
    have hcmap : Continuous (circleMap (0 : ℂ) 1) := by fun_prop
    exact hb.comp_continuous hcmap (fun θ => by
      simpa using circleMap_mem_sphere' (0 : ℂ) 1 θ)
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let K : ℝ × ℝ → ℝ := fun p =>
    Real.log ‖circleMap c ρ p.1 - b (circleMap 0 1 p.2)‖
  have hKint : Integrable K (μ.prod μ) :=
    circle_log_kernel_prod_integrable b hangle M hM c ρ hρ
  have hleftcont : ContinuousOn
      (fun ζ : ℂ => Real.log ‖c - b ζ‖) (sphere (0 : ℂ) 1) := by
    have hdist : ContinuousOn (fun ζ : ℂ => ‖c - b ζ‖)
        (sphere (0 : ℂ) 1) := (continuousOn_const.sub hb).norm
    apply hdist.log
    intro ζ hζ
    have hne : c ≠ b ζ := by
      intro heq
      exact hc ⟨ζ, hζ, heq.symm⟩
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hleft : CircleIntegrable
      (fun ζ : ℂ => Real.log ‖c - b ζ‖) 0 1 := by
    have hcont' : ContinuousOn (fun ζ : ℂ => Real.log ‖c - b ζ‖)
        (sphere (0 : ℂ) |(1 : ℝ)|) := by simpa using hleftcont
    exact hcont'.circleIntegrable'
  have hinner : CircleIntegrable
      (fun ζ : ℂ => Real.circleAverage
        (fun u : ℂ => Real.log ‖u - b ζ‖) c ρ) 0 1 := by
    change IntervalIntegrable
      (fun θ : ℝ => Real.circleAverage
        (fun u : ℂ => Real.log ‖u - b (circleMap 0 1 θ)‖) c ρ)
      volume 0 (2 * Real.pi)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 2 * Real.pi by positivity)]
    change Integrable (fun θ : ℝ => Real.circleAverage
      (fun u : ℂ => Real.log ‖u - b (circleMap 0 1 θ)‖) c ρ) μ
    have heq : (fun θ : ℝ => Real.circleAverage
        (fun u : ℂ => Real.log ‖u - b (circleMap 0 1 θ)‖) c ρ) =
        (fun θ : ℝ => (2 * Real.pi)⁻¹ * ∫ t : ℝ, K (t, θ) ∂μ) := by
      funext θ
      rw [circleAverage_eq_angle_Ioc_general]
    rw [heq]
    exact hKint.integral_prod_right.const_mul _
  have hmono : Real.circleAverage (fun ζ : ℂ => Real.log ‖c - b ζ‖) 0 1 ≤
      Real.circleAverage
        (fun ζ : ℂ => Real.circleAverage
          (fun u : ℂ => Real.log ‖u - b ζ‖) c ρ) 0 1 := by
    apply Real.circleAverage_mono hleft hinner
    intro ζ hζ
    have hne : c ≠ b ζ := by
      intro heq
      exact hc ⟨ζ, by simpa using hζ, heq.symm⟩
    exact log_norm_sub_le_circleAverage_of_ne c (b ζ) ρ hρ hne
  rw [← circleAverage_circleAverage_log_swap b hangle M hM c ρ hρ] at hmono
  exact hmono
end SpringerLean