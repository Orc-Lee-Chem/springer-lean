import SpringerLean.Round11FinalGreen

open MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate

namespace SpringerLean

/-- Cauchy–Schwarz for two actual complex functions on the unit disk,
expressed in ordinary real square-norm integrals. -/
theorem disk_integral_norm_mul_le_sqrt_sq
    (f g : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) 1))
    (hfSq : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1))
    (hgSq : IntegrableOn (fun z : ℂ => ‖g z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1)) :
    (∫ z in Metric.ball (0 : ℂ) 1,
      ‖f z‖ * ‖g z‖ ∂volume) ≤
      Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1,
        ‖f z‖ ^ 2 ∂volume) *
      Real.sqrt (∫ z in Metric.ball (0 : ℂ) 1,
        ‖g z‖ ^ 2 ∂volume) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hfA : AEStronglyMeasurable f μ := hf.aestronglyMeasurable hD
  have hgA : AEStronglyMeasurable g μ := hg.aestronglyMeasurable hD
  have hf2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq_norm hfA).mpr hfSq
  have hg2 : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm hgA).mpr hgSq
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hfn : MemLp (fun z => ‖f z‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf2.norm
  have hgn : MemLp (fun z => ‖g z‖) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hg2.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall (fun z => norm_nonneg (f z)))
    (Filter.Eventually.of_forall (fun z => norm_nonneg (g z)))
    hfn hgn
  simpa [D, μ, Real.sqrt_eq_rpow] using h

/-- The product of the actual derivative with its regularization error tends
to zero in disk `L¹`; this is the Cauchy–Schwarz term in the weighted-area
limit. -/
theorem regular_derivDiff_mul_actual_integral_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        ‖deriv (regularForwardGerm s F) (conj z) -
          deriv (exteriorForwardGerm F) (conj z)‖ *
        ‖deriv (exteriorForwardGerm F) (conj z)‖ ∂volume)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D : Set ℂ := Metric.ball 0 1
  let Q : ℝ → ℝ := fun s => ∫ z in D,
    ‖deriv (regularForwardGerm s F) (conj z) -
      deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume
  let B : ℝ := ∫ z in D,
    ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 ∂volume
  let L : ℝ → ℝ := fun s => ∫ z in D,
    ‖deriv (regularForwardGerm s F) (conj z) -
      deriv (exteriorForwardGerm F) (conj z)‖ *
    ‖deriv (exteriorForwardGerm F) (conj z)‖ ∂volume
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
      (fun s => Real.sqrt (Q s) * Real.sqrt B)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have ht := (Real.continuous_sqrt.tendsto 0).comp hQ
    simpa using ht.mul (tendsto_const_nhds (x := Real.sqrt B))
  have hgCont := exteriorForwardGerm_deriv_conj_continuousOn_unitBall F hc
  have hgSq := (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  have hupper : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      L s ≤ Real.sqrt (Q s) * Real.sqrt B := by
    filter_upwards [h0, h1] with s hs0 hs1
    have hgs : ContinuousOn (deriv (regularForwardGerm s F)) D := by
      rw [regularForwardGerm_eq_actual s hs0 F]
      exact (exteriorForwardGerm_analyticOnNhd_unitBall
        (rescaleExterior s F)
        (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).deriv.continuousOn
    have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℂ => conj z) D D := by
      intro z hz
      simpa only [D, Metric.mem_ball, dist_zero_right,
        ← Complex.star_def, norm_star] using hz
    have hdiffCont := (hgs.comp hcconj.continuousOn hmaps).sub hgCont
    have hdiffSq := (regularForwardGerm_deriv_difference_sq_integrable_le
      F hc hs0 hs1).1
    exact disk_integral_norm_mul_le_sqrt_sq _ _ hdiffCont hgCont hdiffSq hgSq
  have hnonneg : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ L s := by
    filter_upwards [] with s
    exact integral_nonneg (fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact squeeze_zero' hnonneg hupper hroot

/-- Pointwise algebra behind the convergence of squared derivative norms. -/
theorem abs_norm_sq_sub_le (a b : ℂ) :
    |‖a‖ ^ 2 - ‖b‖ ^ 2| ≤
      ‖a - b‖ ^ 2 + 2 * ‖a - b‖ * ‖b‖ := by
  have hnorm : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa only [sub_add_cancel] using norm_add_le (a - b) b
  have hdiff : |‖a‖ - ‖b‖| ≤ ‖a - b‖ :=
    abs_norm_sub_norm_le a b
  have hsum : 0 ≤ ‖a‖ + ‖b‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    |‖a‖ ^ 2 - ‖b‖ ^ 2| =
        |‖a‖ - ‖b‖| * (‖a‖ + ‖b‖) := by
          rw [show ‖a‖ ^ 2 - ‖b‖ ^ 2 =
            (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) by ring,
            abs_mul, abs_of_nonneg hsum]
    _ ≤ ‖a - b‖ * (‖a‖ + ‖b‖) :=
      mul_le_mul_of_nonneg_right hdiff hsum
    _ ≤ ‖a - b‖ * (‖a - b‖ + 2 * ‖b‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      linarith
    _ = ‖a - b‖ ^ 2 + 2 * ‖a - b‖ * ‖b‖ := by ring

/-- Two square-integrable complex functions have an integrable absolute
difference of squared norms on the disk. -/
theorem disk_abs_norm_sq_sub_integrableOn
    (f g : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.ball (0 : ℂ) 1))
    (hg : ContinuousOn g (Metric.ball (0 : ℂ) 1))
    (hfSq : IntegrableOn (fun z : ℂ => ‖f z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1))
    (hgSq : IntegrableOn (fun z : ℂ => ‖g z‖ ^ 2)
      (Metric.ball (0 : ℂ) 1)) :
    IntegrableOn (fun z : ℂ => |‖f z‖ ^ 2 - ‖g z‖ ^ 2|)
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hfA : AEStronglyMeasurable f μ := hf.aestronglyMeasurable hD
  have hgA : AEStronglyMeasurable g μ := hg.aestronglyMeasurable hD
  have hf2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq_norm hfA).mpr hfSq
  have hg2 : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm hgA).mpr hgSq
  have hd2 : MemLp (fun z => f z - g z) 2 μ := hf2.sub hg2
  have hdA : AEStronglyMeasurable (fun z => f z - g z) μ :=
    (hf.sub hg).aestronglyMeasurable hD
  have hdSq : IntegrableOn (fun z => ‖f z - g z‖ ^ 2) D :=
    (memLp_two_iff_integrable_sq_norm hdA).mp hd2
  have hprod : IntegrableOn
      (fun z => ‖f z - g z‖ * ‖g z‖) D := by
    change Integrable (fun z => ‖f z - g z‖ * ‖g z‖) μ
    convert hd2.norm.integrable_mul hg2.norm using 1
  have hright : IntegrableOn
      (fun z => ‖f z - g z‖ ^ 2 +
        2 * (‖f z - g z‖ * ‖g z‖)) D :=
    hdSq.add (hprod.const_mul 2)
  have hleftCont : ContinuousOn
      (fun z => |‖f z‖ ^ 2 - ‖g z‖ ^ 2|) D := by
    fun_prop
  have hleftA : AEStronglyMeasurable
      (fun z => |‖f z‖ ^ 2 - ‖g z‖ ^ 2|) μ :=
    hleftCont.aestronglyMeasurable hD
  apply Integrable.mono_nonneg hright hleftA
  · exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
  · exact Filter.Eventually.of_forall (fun z => by
      simpa [mul_assoc] using abs_norm_sq_sub_le (f z) (g z))

/-- Integrability of the squared-norm difference for the actual exterior
forward germ and its regularization, without boundary analyticity. -/
theorem regular_deriv_sq_difference_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn (fun z : ℂ =>
      |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
        ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2|)
      (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  have hgs : ContinuousOn (deriv (regularForwardGerm s F)) D := by
    rw [regularForwardGerm_eq_actual s hs0 F]
    exact (exteriorForwardGerm_analyticOnNhd_unitBall
      (rescaleExterior s F)
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).deriv.continuousOn
  have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
  have hmaps : Set.MapsTo (fun z : ℂ => conj z) D D := by
    intro z hz
    simpa only [D, Metric.mem_ball, dist_zero_right,
      ← Complex.star_def, norm_star] using hz
  have hfs := hgs.comp hcconj.continuousOn hmaps
  have hg := exteriorForwardGerm_deriv_conj_continuousOn_unitBall F hc
  have hfsSq : IntegrableOn
      (fun z : ℂ => ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2) D := by
    rw [regularForwardGerm_eq_actual s hs0 F]
    exact (exteriorForwardGerm_deriv_sq_integrable_le_one
      (rescaleExterior s F)
      (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).1
  have hgSq := (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  exact disk_abs_norm_sq_sub_integrableOn _ _ hfs hg hfsSq hgSq

/-- Actual squared derivative norms converge in `L¹(D)` as `s ↑ 1`.
This is stronger than convergence of their unweighted integrals. -/
theorem regular_deriv_sq_difference_L1_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
          ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2| ∂volume)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  let g : ℂ → ℂ := fun z => deriv (exteriorForwardGerm F) (conj z)
  let d : ℝ → ℂ → ℂ := fun s z =>
    deriv (regularForwardGerm s F) (conj z) - g z
  let Q : ℝ → ℝ := fun s => ∫ z in D, ‖d s z‖ ^ 2 ∂volume
  let L : ℝ → ℝ := fun s => ∫ z in D, ‖d s z‖ * ‖g z‖ ∂volume
  let S : ℝ → ℝ := fun s => ∫ z in D,
    |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
      ‖g z‖ ^ 2| ∂volume
  have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hQ : Tendsto Q (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h := regularForwardGerm_deriv_L2_tendsto F hc
    have ht := (tendsto_const_nhds (x := Real.pi)).mul h
    convert ht using 1
    · funext s
      dsimp [Q, D, d, g]
      field_simp [Real.pi_ne_zero]
    · simp
  have hL : Tendsto L (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    regular_derivDiff_mul_actual_integral_tendsto_zero F hc
  have hright : Tendsto (fun s => Q s + 2 * L s)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hQ.add ((tendsto_const_nhds (x := (2 : ℝ))).mul hL)
  have hgCont := exteriorForwardGerm_deriv_conj_continuousOn_unitBall F hc
  have hgSq := (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  have hupper : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      S s ≤ Q s + 2 * L s := by
    filter_upwards [h0, h1] with s hs0 hs1
    have hgs : ContinuousOn (deriv (regularForwardGerm s F)) D := by
      rw [regularForwardGerm_eq_actual s hs0 F]
      exact (exteriorForwardGerm_analyticOnNhd_unitBall
        (rescaleExterior s F)
        (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).deriv.continuousOn
    have hcconj : Continuous (fun z : ℂ => conj z) := by fun_prop
    have hmaps : Set.MapsTo (fun z : ℂ => conj z) D D := by
      intro z hz
      simpa only [D, Metric.mem_ball, dist_zero_right,
        ← Complex.star_def, norm_star] using hz
    have hdCont : ContinuousOn (d s) D :=
      (hgs.comp hcconj.continuousOn hmaps).sub hgCont
    have hdSq := (regularForwardGerm_deriv_difference_sq_integrable_le
      F hc hs0 hs1).1
    have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
    have hdA : AEStronglyMeasurable (d s) μ :=
      hdCont.aestronglyMeasurable hD
    have hgA : AEStronglyMeasurable g μ :=
      hgCont.aestronglyMeasurable hD
    have hd2 : MemLp (d s) 2 μ :=
      (memLp_two_iff_integrable_sq_norm hdA).mpr hdSq
    have hg2 : MemLp g 2 μ :=
      (memLp_two_iff_integrable_sq_norm hgA).mpr hgSq
    have hprod : IntegrableOn (fun z => ‖d s z‖ * ‖g z‖) D := by
      change Integrable (fun z => ‖d s z‖ * ‖g z‖) μ
      convert hd2.norm.integrable_mul hg2.norm using 1
    have hrightInt : IntegrableOn
        (fun z => ‖d s z‖ ^ 2 + 2 * (‖d s z‖ * ‖g z‖)) D :=
      hdSq.add (hprod.const_mul 2)
    have hle : S s ≤
        ∫ z in D, ‖d s z‖ ^ 2 +
          2 * (‖d s z‖ * ‖g z‖) ∂volume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun z => abs_nonneg _)
      · exact hrightInt
      · exact Filter.Eventually.of_forall (fun z => by
          dsimp [d, g]
          simpa [mul_assoc] using
            abs_norm_sq_sub_le
              (deriv (regularForwardGerm s F) (conj z))
              (deriv (exteriorForwardGerm F) (conj z)))
    have heq :
        (∫ z in D, ‖d s z‖ ^ 2 +
          2 * (‖d s z‖ * ‖g z‖) ∂volume) =
        Q s + 2 * L s := by
      rw [integral_add hdSq (hprod.const_mul 2), integral_const_mul]
    exact hle.trans_eq heq
  have hnonneg : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ S s := by
    filter_upwards [] with s
    exact integral_nonneg (fun z => abs_nonneg _)
  exact squeeze_zero' hnonneg hupper hright

/-- The uniformly bounded harmonic weight preserves the `L¹` convergence
of the squared derivative norms. -/
theorem regular_weighted_deriv_sq_difference_L1_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ m *
          |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
            ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2| ∂volume)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D : Set ℂ := Metric.ball 0 1
  let S : ℝ → ℝ := fun s => ∫ z in D,
    |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
      ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2| ∂volume
  let V : ℝ → ℝ := fun s => ∫ z in D,
    ‖regularHarmonic s F z‖ ^ m *
      |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
        ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2| ∂volume
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound F hc
  have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hS : Tendsto S (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    regular_deriv_sq_difference_L1_tendsto_zero F hc
  have hroot : Tendsto (fun s => C ^ m * S s)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := C ^ m)).mul hS
  have hupper : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      V s ≤ C ^ m * S s := by
    filter_upwards [h0, h1] with s hs0 hs1
    have hInt := regular_deriv_sq_difference_integrableOn
      F hc hs0 hs1
    have hle : V s ≤
        ∫ z in D, C ^ m *
          |‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2 -
            ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2| ∂volume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun z =>
          mul_nonneg (pow_nonneg (norm_nonneg _) _) (abs_nonneg _))
      · exact hInt.const_mul (C ^ m)
      · filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet]
          with z hz
        have hz' : ‖z‖ < 1 := by
          simpa only [D, Metric.mem_ball, dist_zero_right] using hz
        have hweight : ‖regularHarmonic s F z‖ ^ m ≤ C ^ m :=
          pow_le_pow_left₀ (norm_nonneg _)
            (hC s hs0 hs1 z hz') m
        exact mul_le_mul_of_nonneg_right hweight (abs_nonneg _)
    simpa only [integral_const_mul] using hle
  have hnonneg : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ V s := by
    filter_upwards [] with s
    exact integral_nonneg (fun z =>
      mul_nonneg (pow_nonneg (norm_nonneg _) _) (abs_nonneg _))
  exact squeeze_zero' hnonneg hupper hroot

end SpringerLean
