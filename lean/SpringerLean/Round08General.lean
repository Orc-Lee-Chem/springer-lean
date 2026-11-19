import SpringerLean.Round08Lp

open MeasureTheory Filter
open scoped Topology ComplexConjugate ENNReal

namespace SpringerLean

noncomputable def actualHarmonic (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  z + exteriorForwardGerm F (conj z)

theorem actualHarmonic_continuousOn_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ContinuousOn (actualHarmonic F) (Metric.ball (0 : ℂ) 1) := by
  have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn
  have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => conj z)
      (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  exact continuousOn_id.add (hg.comp hcconj.continuousOn hmaps)

theorem regularHarmonic_continuousOn_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ContinuousOn (regularHarmonic s F) (Metric.ball (0 : ℂ) 1) := by
  have hgs : ContinuousOn (regularForwardGerm s F)
      (Metric.ball (0 : ℂ) 1) := by
    rw [regularForwardGerm_eq_actual s hs0 F]
    exact (exteriorForwardGerm_analyticOnNhd_unitBall
      (rescaleExterior s F)
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).continuousOn
  have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => conj z)
      (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  exact continuousOn_id.add (hgs.comp hcconj.continuousOn hmaps)

theorem exteriorForwardGerm_deriv_conj_continuousOn_unitBall
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ContinuousOn
      (fun z : ℂ => deriv (exteriorForwardGerm F) (conj z))
      (Metric.ball (0 : ℂ) 1) := by
  have hg := (exteriorForwardGerm_analyticOnNhd_unitBall F hc).deriv.continuousOn
  have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => conj z)
      (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    simpa only [Metric.mem_ball, dist_zero_right, ← Complex.star_def, norm_star] using hz
  exact hg.comp hcconj.continuousOn hmaps

/-- Dominated convergence for the factor containing the fixed, actual
derivative. The variable factor is a uniformly bounded harmonic filling. -/
theorem regularHarmonic_power_actualDeriv_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (p : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        regularHarmonic s F z ^ p *
          deriv (exteriorForwardGerm F) (conj z) ∂volume)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z in Metric.ball (0 : ℂ) 1,
        actualHarmonic F z ^ p *
          deriv (exteriorForwardGerm F) (conj z) ∂volume)) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound F hc
  have hgInt := exteriorForwardGerm_deriv_integrableOn F hc
  have hgCont := exteriorForwardGerm_deriv_conj_continuousOn_unitBall F hc
  have hdom : Integrable
      (fun z : ℂ => C ^ p * ‖deriv (exteriorForwardGerm F) (conj z)‖) μ :=
    hgInt.norm.const_mul _
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbelow : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hmeas : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun z : ℂ => regularHarmonic s F z ^ p *
          deriv (exteriorForwardGerm F) (conj z)) μ := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    exact (((regularHarmonic_continuousOn_unitBall F hc hs0 hs1).pow p).mul
      hgCont).aestronglyMeasurable hD
  have hbound : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ z ∂μ,
        ‖regularHarmonic s F z ^ p *
          deriv (exteriorForwardGerm F) (conj z)‖ ≤
        C ^ p * ‖deriv (exteriorForwardGerm F) (conj z)‖ := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    filter_upwards [ae_restrict_mem hD] with z hz
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (hC s hs0 hs1 z (by
        simpa only [D, Metric.mem_ball, dist_zero_right] using hz)) p)
      (norm_nonneg _)
  have hpoint : ∀ᵐ z ∂μ,
      Tendsto
        (fun s : ℝ => regularHarmonic s F z ^ p *
          deriv (exteriorForwardGerm F) (conj z))
        (𝓝[<] (1 : ℝ))
        (𝓝 (actualHarmonic F z ^ p *
          deriv (exteriorForwardGerm F) (conj z))) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    have hz' : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have ht := (regularHarmonic_tendsto F hc hz').pow p
    simpa only [actualHarmonic] using
      ht.mul (tendsto_const_nhds
        (x := deriv (exteriorForwardGerm F) (conj z)))
  exact tendsto_integral_filter_of_dominated_convergence
    (fun z : ℂ => C ^ p * ‖deriv (exteriorForwardGerm F) (conj z)‖)
    hmeas hbound hdom hpoint

/-- The derivative-difference term vanishes in complex integral, using the
uniform filling bound and the proved `L¹` derivative convergence. -/
theorem regularHarmonic_power_derivDiff_integral_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (p : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        regularHarmonic s F z ^ p *
          (deriv (regularForwardGerm s F) (conj z) -
            deriv (exteriorForwardGerm F) (conj z)) ∂volume)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound F hc
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbelow : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hright : Tendsto
      (fun s : ℝ => C ^ p *
        (∫ z in D,
          ‖deriv (regularForwardGerm s F) (conj z) -
            deriv (exteriorForwardGerm F) (conj z)‖ ∂volume))
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (regularForwardGerm_deriv_L1_tendsto F hc))
  have hupper : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ‖∫ z in D,
          regularHarmonic s F z ^ p *
            (deriv (regularForwardGerm s F) (conj z) -
              deriv (exteriorForwardGerm F) (conj z)) ∂volume‖ ≤
      C ^ p * (∫ z in D,
        ‖deriv (regularForwardGerm s F) (conj z) -
          deriv (exteriorForwardGerm F) (conj z)‖ ∂volume) := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    let diff : ℂ → ℂ := fun z =>
      deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z)
    let H : ℂ → ℂ := regularHarmonic s F
    have hdiffInt : Integrable diff μ :=
      regularForwardGerm_deriv_difference_integrableOn F hc hs0 hs1
    have hHcont : ContinuousOn H D :=
      regularHarmonic_continuousOn_unitBall F hc hs0 hs1
    have hHmeas : AEStronglyMeasurable (fun z => H z ^ p) μ :=
      (hHcont.pow p).aestronglyMeasurable hD
    have hHbound : ∀ᵐ z ∂μ, ‖H z ^ p‖ ≤ C ^ p := by
      filter_upwards [ae_restrict_mem hD] with z hz
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hC s hs0 hs1 z (by
          simpa only [D, Metric.mem_ball, dist_zero_right] using hz)) p
    have hprodInt : Integrable (fun z => H z ^ p * diff z) μ :=
      hdiffInt.bdd_mul hHmeas hHbound
    have hnormInt : Integrable (fun z => ‖H z ^ p * diff z‖) μ :=
      hprodInt.norm
    have hmajorInt : Integrable (fun z => C ^ p * ‖diff z‖) μ :=
      hdiffInt.norm.const_mul _
    have hmono : (∫ z, ‖H z ^ p * diff z‖ ∂μ) ≤
        ∫ z, C ^ p * ‖diff z‖ ∂μ := by
      apply integral_mono_ae hnormInt hmajorInt
      filter_upwards [hHbound] with z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    calc
      ‖∫ z in D, H z ^ p * diff z ∂volume‖ ≤
          ∫ z in D, ‖H z ^ p * diff z‖ ∂volume :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ z in D, C ^ p * ‖diff z‖ ∂volume := hmono
      _ = C ^ p * ∫ z in D, ‖diff z‖ ∂volume := by
        rw [integral_const_mul]
  have hnonneg : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      0 ≤ ‖∫ z in D,
          regularHarmonic s F z ^ p *
            (deriv (regularForwardGerm s F) (conj z) -
              deriv (exteriorForwardGerm F) (conj z)) ∂volume‖ := by
    filter_upwards [] with s
    exact norm_nonneg _
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' hnonneg hupper hright)

/-- The full regularized complex integral converges to the integral formed
from the same actual, unregularized exterior map. -/
theorem regularHarmonic_full_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (p : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        regularHarmonic s F z ^ p *
          deriv (regularForwardGerm s F) (conj z) ∂volume)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z in Metric.ball (0 : ℂ) 1,
        actualHarmonic F z ^ p *
          deriv (exteriorForwardGerm F) (conj z) ∂volume)) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound F hc
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbelow : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hEq : (fun s : ℝ => ∫ z in D,
        regularHarmonic s F z ^ p *
          deriv (regularForwardGerm s F) (conj z) ∂volume) =ᶠ[𝓝[<] (1 : ℝ)]
      (fun s : ℝ =>
        (∫ z in D, regularHarmonic s F z ^ p *
          (deriv (regularForwardGerm s F) (conj z) -
            deriv (exteriorForwardGerm F) (conj z)) ∂volume) +
        (∫ z in D, regularHarmonic s F z ^ p *
          deriv (exteriorForwardGerm F) (conj z) ∂volume)) := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    let H : ℂ → ℂ := regularHarmonic s F
    let diff : ℂ → ℂ := fun z =>
      deriv (regularForwardGerm s F) (conj z) -
        deriv (exteriorForwardGerm F) (conj z)
    let gder : ℂ → ℂ := fun z => deriv (exteriorForwardGerm F) (conj z)
    have hHcont : ContinuousOn H D :=
      regularHarmonic_continuousOn_unitBall F hc hs0 hs1
    have hHmeas : AEStronglyMeasurable (fun z => H z ^ p) μ :=
      (hHcont.pow p).aestronglyMeasurable hD
    have hHbound : ∀ᵐ z ∂μ, ‖H z ^ p‖ ≤ C ^ p := by
      filter_upwards [ae_restrict_mem hD] with z hz
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hC s hs0 hs1 z (by
          simpa only [D, Metric.mem_ball, dist_zero_right] using hz)) p
    have hdiffInt : Integrable diff μ :=
      regularForwardGerm_deriv_difference_integrableOn F hc hs0 hs1
    have hgInt : Integrable gder μ := exteriorForwardGerm_deriv_integrableOn F hc
    have h1Int : Integrable (fun z => H z ^ p * diff z) μ :=
      hdiffInt.bdd_mul hHmeas hHbound
    have h2Int : Integrable (fun z => H z ^ p * gder z) μ :=
      hgInt.bdd_mul hHmeas hHbound
    calc
      (∫ z in D, H z ^ p * deriv (regularForwardGerm s F) (conj z) ∂volume) =
          ∫ z in D, (H z ^ p * diff z + H z ^ p * gder z) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with z
            dsimp [diff, gder]
            ring
      _ = (∫ z in D, H z ^ p * diff z ∂volume) +
            (∫ z in D, H z ^ p * gder z ∂volume) :=
          integral_add h1Int h2Int
  have hlim1 := regularHarmonic_power_derivDiff_integral_tendsto_zero F hc p
  have hlim2 := regularHarmonic_power_actualDeriv_integral_tendsto F hc p
  have hlim := hlim1.add hlim2
  simpa only [zero_add, D] using hlim.congr' hEq.symm

/-- Lemma 3.1's first complex area identity for every actual paper-class
map, with its original independent inverse coefficient and no extra premise. -/
theorem exteriorInverseCoeff_eq_actualHarmonic_diskIntegral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {n : ℕ} (hn : 1 ≤ n) :
    exteriorInverseCoeff F n =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          (z + exteriorForwardGerm F (conj z)) ^ (n - 1) *
            deriv (exteriorForwardGerm F) (conj z) ∂volume) := by
  have hcoef := regularHarmonic_first_integral_tendsto F hc hn
  have hint := (tendsto_const_nhds
    (x := (Real.pi : ℂ)⁻¹)).mul
      (regularHarmonic_full_integral_tendsto F hc (n - 1))
  have hsame := tendsto_nhds_unique hcoef hint
  simpa only [actualHarmonic] using hsame

/-- The original odd-order statement of the first identity in Lemma 3.1. -/
theorem exteriorInverseCoeff_odd_eq_actualHarmonic_diskIntegral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) :
    exteriorInverseCoeff F (2 * k - 1) =
      (Real.pi : ℂ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          (z + exteriorForwardGerm F (conj z)) ^ (2 * k - 2) *
            deriv (exteriorForwardGerm F) (conj z) ∂volume) := by
  have hn : 1 ≤ 2 * k - 1 := by omega
  simpa only [show (2 * k - 1) - 1 = 2 * k - 2 by omega] using
    exteriorInverseCoeff_eq_actualHarmonic_diskIntegral F hc hn

/-- Low-order check: the unregularized complex disk integral reads `b₁`. -/
theorem actualHarmonic_first_identity_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        deriv (exteriorForwardGerm F) (conj z) ∂volume) =
      exteriorForwardCoeff F 1 := by
  have h := exteriorInverseCoeff_eq_actualHarmonic_diskIntegral
    F hc (n := 1) (by omega)
  simp only [Nat.sub_self, pow_zero, one_mul] at h
  rw [exteriorInverseCoeff_one_eq_forwardCoeff_one F hc] at h
  exact h.symm

/-- Low-order check: the unregularized order-three integral reads
`b₃+b₁²` for the same actual map. -/
theorem actualHarmonic_first_identity_three
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        (z + exteriorForwardGerm F (conj z)) ^ 2 *
          deriv (exteriorForwardGerm F) (conj z) ∂volume) =
      exteriorForwardCoeff F 3 + (exteriorForwardCoeff F 1) ^ 2 := by
  have h := exteriorInverseCoeff_eq_actualHarmonic_diskIntegral
    F hc (n := 3) (by omega)
  rw [exteriorInverseCoeff_three_eq_forward F hc] at h
  simpa using h.symm

end SpringerLean
