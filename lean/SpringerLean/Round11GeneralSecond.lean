import SpringerLean.Round11L2
import SpringerLean.Round09OmittedLimit
import SpringerLean.Round11FinalGreen

open MeasureTheory Filter
open scoped Topology ComplexConjugate ENNReal

namespace SpringerLean

/-- Multiplication by a bounded continuous real weight preserves ordinary
disk integrability. -/
theorem disk_integrable_bounded_weight_mul
    (w f : ℂ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ContinuousOn w (Metric.ball (0 : ℂ) 1))
    (hf : IntegrableOn f (Metric.ball (0 : ℂ) 1))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 1, |w z| ≤ C) :
    IntegrableOn (fun z => w z * f z) (Metric.ball (0 : ℂ) 1) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hwa : AEStronglyMeasurable w μ := hw.aestronglyMeasurable hD
  have hfa : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have hprod : AEStronglyMeasurable (fun z => w z * f z) μ :=
    hwa.mul hfa
  have hdom : Integrable (fun z => C * |f z|) μ :=
    hf.norm.const_mul C
  apply Integrable.mono' hdom hprod
  filter_upwards [ae_restrict_mem hD] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hbound z hz) (abs_nonneg _)

/-- Dominated convergence for the fixed actual derivative factor in the
weighted second area integral. -/
theorem regular_weighted_actualDeriv_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
          ∂volume)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
          ∂volume)) := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound F hc
  have hgSq := (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  have hgCont := exteriorForwardGerm_deriv_conj_continuousOn_unitBall F hc
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol
  have hdom : Integrable
      (fun z : ℂ => C ^ m *
        (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)) μ := by
    have hsum : Integrable
        (fun z : ℂ => 1 +
          ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2) μ :=
      (integrable_const (1 : ℝ)).add hgSq
    exact hsum.const_mul _
  have hpos : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbelow : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hmeas : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      AEStronglyMeasurable
        (fun z : ℂ => ‖regularHarmonic s F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)) μ := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    have hcont : ContinuousOn
        (fun z : ℂ => ‖regularHarmonic s F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)) D :=
      (((regularHarmonic_continuousOn_unitBall F hc hs0 hs1).norm).pow m).mul
        (continuousOn_const.sub (hgCont.norm.pow 2))
    exact hcont.aestronglyMeasurable hD
  have hbound : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ∀ᵐ z ∂μ,
        ‖‖regularHarmonic s F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)‖ ≤
        C ^ m * (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2) := by
    filter_upwards [hpos, hbelow] with s hs0 hs1
    filter_upwards [ae_restrict_mem hD] with z hz
    have hz' : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have hweight : ‖regularHarmonic s F z‖ ^ m ≤ C ^ m :=
      pow_le_pow_left₀ (norm_nonneg _) (hC s hs0 hs1 z hz') m
    have hsquare : 0 ≤ ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 :=
      sq_nonneg _
    have habs : |1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2| ≤
        1 + ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact (mul_le_mul hweight habs (abs_nonneg _) (pow_nonneg hC0 _))
  have hpoint : ∀ᵐ z ∂μ,
      Tendsto
        (fun s : ℝ => ‖regularHarmonic s F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2))
        (𝓝[<] (1 : ℝ))
        (𝓝 (‖actualHarmonic F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2))) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    have hz' : ‖z‖ < 1 := by
      simpa only [D, Metric.mem_ball, dist_zero_right] using hz
    have ht := (regularHarmonic_tendsto F hc hz').norm.pow m
    simpa only [actualHarmonic] using ht.mul
      (tendsto_const_nhds (x :=
        1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2))
  exact tendsto_integral_filter_of_dominated_convergence
    (fun z : ℂ => C ^ m *
      (1 + ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2))
    hmeas hbound hdom hpoint

/-- The signed error made by replacing the regularized derivative square by
the actual derivative square vanishes after the harmonic weight is inserted. -/
theorem regular_weighted_derivError_integral_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ m *
          (‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2 -
            ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2)
          ∂volume)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  let D : Set ℂ := Metric.ball 0 1
  let w : ℝ → ℂ → ℝ := fun s z => ‖regularHarmonic s F z‖ ^ m
  let a : ℝ → ℂ → ℝ := fun s z =>
    ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2
  let b : ℂ → ℝ := fun z =>
    ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2
  let E : ℝ → ℝ := fun s => ∫ z in D, w s z * (b z - a s z) ∂volume
  let V : ℝ → ℝ := fun s => ∫ z in D, w s z * |a s z - b z| ∂volume
  have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hV : Tendsto V (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    regular_weighted_deriv_sq_difference_L1_tendsto_zero F hc m
  have hupper : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), |E s| ≤ V s := by
    filter_upwards [h0, h1] with s hs0 hs1
    have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
    have hnorm := (abs_integral_le_integral_abs
      (μ := volume.restrict D) (f := fun z => w s z * (b z - a s z)))
    have hright :
        (∫ z in D, |w s z * (b z - a s z)| ∂volume) = V s := by
      apply setIntegral_congr_fun hD
      intro z hz
      dsimp [w, a, b]
      rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), abs_sub_comm]
    exact hnorm.trans_eq hright
  have habs : Tendsto (fun s => |E s|)
      (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
    · filter_upwards [] with s
      exact abs_nonneg _
    · exact hupper
    · exact hV
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using habs

/-- The full signed weighted disk integral for the actual regularizations
converges to the harmonic filling of the original exterior map. -/
theorem regular_weighted_signedDisk_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    Tendsto
      (fun s : ℝ => ∫ z in Metric.ball (0 : ℂ) 1,
        ‖regularHarmonic s F z‖ ^ m *
          (1 - ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2)
          ∂volume)
      (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ m *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
          ∂volume)) := by
  let D : Set ℂ := Metric.ball 0 1
  let w : ℝ → ℂ → ℝ := fun s z => ‖regularHarmonic s F z‖ ^ m
  let a : ℝ → ℂ → ℝ := fun s z =>
    ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2
  let b : ℂ → ℝ := fun z =>
    ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2
  let I : ℝ → ℝ := fun s => ∫ z in D, w s z * (1 - a s z) ∂volume
  let J : ℝ → ℝ := fun s => ∫ z in D, w s z * (1 - b z) ∂volume
  let E : ℝ → ℝ := fun s => ∫ z in D, w s z * (b z - a s z) ∂volume
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound F hc
  have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 < s :=
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have h1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hgSq : IntegrableOn b D := by
    exact (exteriorForwardGerm_deriv_sq_integrable_le_one F hc).1
  have hvol : volume D ≠ ∞ := by
    rw [Complex.volume_ball]
    finiteness
  haveI : IsFiniteMeasure (volume.restrict D) :=
    isFiniteMeasure_restrict.mpr hvol
  have hJbase : IntegrableOn (fun z => 1 - b z) D :=
    (integrable_const (1 : ℝ)).sub hgSq
  have hsplit : ∀ s : ℝ, 0 < s → s < 1 →
      I s = J s + E s := by
    intro s hs0 hs1
    have haSq : IntegrableOn (a s) D := by
      change IntegrableOn (fun z : ℂ =>
        ‖deriv (regularForwardGerm s F) (conj z)‖ ^ 2) D
      rw [regularForwardGerm_eq_actual s hs0 F]
      exact (exteriorForwardGerm_deriv_sq_integrable_le_one
        (rescaleExterior s F)
        (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)).1
    have hEbase : IntegrableOn (fun z => b z - a s z) D :=
      hgSq.sub haSq
    have hwCont : ContinuousOn (w s) D :=
      (regularHarmonic_continuousOn_unitBall F hc hs0 hs1).norm.pow m
    have hwBound : ∀ z ∈ D, |w s z| ≤ C ^ m := by
      intro z hz
      have hz' : ‖z‖ < 1 := by
        simpa only [D, Metric.mem_ball, dist_zero_right] using hz
      rw [abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hC s hs0 hs1 z hz') m
    have hJInt := disk_integrable_bounded_weight_mul
      (w s) (fun z => 1 - b z) (C ^ m) (pow_nonneg hC0 _)
      hwCont hJbase hwBound
    have hEInt := disk_integrable_bounded_weight_mul
      (w s) (fun z => b z - a s z) (C ^ m) (pow_nonneg hC0 _)
      hwCont hEbase hwBound
    have hpoint :
        (∫ z in D, w s z * (1 - a s z) ∂volume) =
        ∫ z in D,
          w s z * (1 - b z) + w s z * (b z - a s z) ∂volume := by
      apply setIntegral_congr_fun Metric.isOpen_ball.measurableSet
      intro z hz
      ring
    calc
      I s = ∫ z in D,
          w s z * (1 - b z) + w s z * (b z - a s z)
          ∂volume := hpoint
      _ = J s + E s := integral_add hJInt hEInt
  have hJ : Tendsto J (𝓝[<] (1 : ℝ))
      (𝓝 (∫ z in D, ‖actualHarmonic F z‖ ^ m *
        (1 - b z) ∂volume)) :=
    regular_weighted_actualDeriv_integral_tendsto F hc m
  have hE : Tendsto E (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    regular_weighted_derivError_integral_tendsto_zero F hc m
  have heq : I =ᶠ[𝓝[<] (1 : ℝ)] (fun s => J s + E s) := by
    filter_upwards [h0, h1] with s hs0 hs1
    exact hsplit s hs0 hs1
  have hlim := hJ.add hE
  simpa only [add_zero, I, J, E, D, w, a, b] using
    hlim.congr' heq.symm

/-- The second identity of Lemma 3.1 for the original centered exterior
map. Both integrals use the actual harmonic filling and actual omitted set. -/
theorem actualWeightedOmittedArea_eq
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) :
    (Real.pi : ℝ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖actualHarmonic F z‖ ^ (2 * k - 2) *
          (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
          ∂volume) =
    (Real.pi : ℝ)⁻¹ *
      (∫ w in exteriorOmitted F,
        ‖w‖ ^ (2 * k - 2) ∂volume) := by
  let m : ℕ := 2 * k - 2
  have hs : Tendsto omittedScaleSeq atTop (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨omittedScaleSeq_tendsto_one,
      Filter.Eventually.of_forall (fun n => omittedScaleSeq_lt_one n)⟩
  have hD := (regular_weighted_signedDisk_integral_tendsto F hc m).comp hs
  have hK := rescaleExterior_omitted_weighted_integral_tendsto F hc m
  have hD' : Tendsto
      (fun n : ℕ => (Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖regularHarmonic (omittedScaleSeq n) F z‖ ^ m *
            (1 - ‖deriv (regularForwardGerm (omittedScaleSeq n) F)
              (conj z)‖ ^ 2) ∂volume))
      atTop
      (𝓝 ((Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖actualHarmonic F z‖ ^ m *
            (1 - ‖deriv (exteriorForwardGerm F) (conj z)‖ ^ 2)
            ∂volume))) := by
    simpa only [Function.comp_def] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (Real.pi : ℝ)⁻¹)
        atTop (𝓝 ((Real.pi : ℝ)⁻¹))).mul hD)
  have hK' : Tendsto
      (fun n : ℕ => (Real.pi : ℝ)⁻¹ *
        (∫ w in exteriorOmitted (rescaleExterior (omittedScaleSeq n) F),
          ‖w‖ ^ m ∂volume))
      atTop
      (𝓝 ((Real.pi : ℝ)⁻¹ *
        (∫ w in exteriorOmitted F, ‖w‖ ^ m ∂volume))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (Real.pi : ℝ)⁻¹)
      atTop (𝓝 ((Real.pi : ℝ)⁻¹))).mul hK
  have hpoint : ∀ n : ℕ,
      (Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖regularHarmonic (omittedScaleSeq n) F z‖ ^ m *
            (1 - ‖deriv (regularForwardGerm (omittedScaleSeq n) F)
              (conj z)‖ ^ 2) ∂volume) =
      (Real.pi : ℝ)⁻¹ *
        (∫ w in exteriorOmitted (rescaleExterior (omittedScaleSeq n) F),
          ‖w‖ ^ m ∂volume) := by
    intro n
    exact regularWeightedOmittedArea_eq F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) hk
  have hlim := tendsto_nhds_unique hD'
    ((show Tendsto
      (fun n : ℕ => (Real.pi : ℝ)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1,
          ‖regularHarmonic (omittedScaleSeq n) F z‖ ^ m *
            (1 - ‖deriv (regularForwardGerm (omittedScaleSeq n) F)
              (conj z)‖ ^ 2) ∂volume))
      atTop
      (𝓝 ((Real.pi : ℝ)⁻¹ *
        (∫ w in exteriorOmitted F, ‖w‖ ^ m ∂volume))) from by
          exact hK'.congr' (Filter.Eventually.of_forall
            (fun n => (hpoint n).symm))))
  simpa only [m] using hlim

end SpringerLean
