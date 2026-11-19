import SpringerLean.Round08Actual

open MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate

namespace SpringerLean

/-- On the finite unit disk, a continuous function with integrable square
norm is integrable. -/
theorem disk_integrable_of_sq_integrable
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (hSq : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1)) :
    IntegrableOn f (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  let μ : Measure ℂ := volume.restrict D
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol
  have hA : AEStronglyMeasurable f μ := hf.aestronglyMeasurable hD
  have h2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq_norm hA).mpr hSq
  exact h2.integrable (by norm_num)

/-- Cauchy–Schwarz against the constant function one on the disk. -/
theorem disk_integral_norm_le_sqrt_sq
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (hSq : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ∂volume) ≤
      Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1, ‖f z‖ ^ 2 ∂volume) *
        Real.sqrt ((volume.restrict (Metric.ball (0 : ℂ) 1)).real Set.univ) := by
  let D : Set ℂ := Metric.ball 0 1
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  let μ : Measure ℂ := volume.restrict D
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol
  have hA : AEStronglyMeasurable f μ := hf.aestronglyMeasurable hD
  have h2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq_norm hA).mpr hSq
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hf2 : MemLp (fun z => ‖f z‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using h2.norm
  have hg2 : MemLp (fun _ : ℂ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : ℂ => (1 : ℝ)) 2 μ)
  have hg0 : 0 ≤ᵐ[μ] (fun _ : ℂ => (1 : ℝ)) :=
    Filter.Eventually.of_forall (by intro z; norm_num)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun z => norm_nonneg (f z)))
    hg0 hf2 hg2
  simpa [D, μ, Real.sqrt_eq_rpow] using h

/-- Strong `L²(D)` convergence implies `L¹(D)` convergence for the actual
derivative difference on the finite disk. -/
theorem regularForwardGerm_deriv_L1_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (regularForwardGerm s F) (conj z) -
          deriv (exteriorForwardGerm F) (conj z)‖ ∂volume)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  let Q : ℝ → ℝ := fun s => ∫ z in D,
    ‖deriv (regularForwardGerm s F) (conj z) -
      deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume
  let L : ℝ → ℝ := fun s => ∫ z in D,
    ‖deriv (regularForwardGerm s F) (conj z) -
      deriv (exteriorForwardGerm F) (conj z)‖ ∂volume
  have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hQ : Tendsto Q (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := regularForwardGerm_deriv_L2_tendsto F hc
    have ht := (tendsto_const_nhds (x := Real.pi)).mul h
    convert ht using 1
    · funext s
      dsimp [Q, D]
      field_simp [Real.pi_ne_zero]
    · simp
  have hroot : Tendsto
      (fun s => Real.sqrt (Q s) * Real.sqrt (μ.real Set.univ))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := (Real.continuous_sqrt.tendsto 0).comp hQ
    simpa [Function.comp_def] using
      ht.mul (tendsto_const_nhds (x := Real.sqrt (μ.real Set.univ)))
  have hupper : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      L s ≤ Real.sqrt (Q s) * Real.sqrt (μ.real Set.univ) := by
    filter_upwards [h0, h1] with s hs0 hs1
    have hgs : ContinuousOn (deriv (regularForwardGerm s F)) D := by
      rw [regularForwardGerm_eq_actual s hs0 F]
      exact (exteriorForwardGerm_analyticOnNhd_unitBall
        (rescaleExterior s F)
        (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).deriv.continuousOn
    have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn
    have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℂ => conj z) D D := by
      intro z hz
      simpa only [D, Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
    have hcont := (hgs.comp hcconj.continuousOn hmaps).sub
      (hg.comp hcconj.continuousOn hmaps)
    have hSq := (regularForwardGerm_deriv_difference_sq_integrable_le
      F hc hs0 hs1).1
    exact disk_integral_norm_le_sqrt_sq _ hcont hSq
  have hnonneg : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ L s := by
    filter_upwards [] with s
    exact integral_nonneg (fun z => norm_nonneg _)
  exact squeeze_zero' hnonneg hupper hroot

/-- The actual derivative is integrable on the unit disk, as required by
the complex first area integral. -/
theorem exteriorForwardGerm_deriv_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    IntegrableOn
      (fun z : ℂ => deriv (exteriorForwardGerm F) (conj z))
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn
  have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => conj z) D D := by
    intro z hz
    simpa only [D, Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  have hcont := hg.comp hcconj.continuousOn hmaps
  exact disk_integrable_of_sq_integrable _ hcont
    (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1

/-- For each regularization parameter the actual derivative difference is
integrable, with no artificial global boundary regularity assumption. -/
theorem regularForwardGerm_deriv_difference_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn
      (fun z : ℂ => deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z))
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  have hgs : ContinuousOn (deriv (regularForwardGerm s F)) D := by
    rw [regularForwardGerm_eq_actual s hs0 F]
    exact (exteriorForwardGerm_analyticOnNhd_unitBall
      (rescaleExterior s F)
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).deriv.continuousOn
  have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn
  have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => conj z) D D := by
    intro z hz
    simpa only [D, Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  have hcont := (hgs.comp hcconj.continuousOn hmaps).sub
    (hg.comp hcconj.continuousOn hmaps)
  exact disk_integrable_of_sq_integrable _ hcont
    (regularForwardGerm_deriv_difference_sq_integrable_le F hc hs0 hs1).1

end SpringerLean
