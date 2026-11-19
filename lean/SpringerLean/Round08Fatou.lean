import SpringerLean.Round08Finite

open MeasureTheory Filter
open scoped Topology ComplexConjugate ENNReal

namespace SpringerLean

/-- Fatou's lemma upgrades finite disk Parseval to a square-integrable
pointwise limit of derivative modes on the open unit disk. -/
theorem disk_derivative_modes_fatou
    (d : ℕ → ℂ) (h : ℂ → ℂ)
    (hcont : ContinuousOn h (Metric.ball (0 : ℂ) 1))
    (hpoint : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      HasSum (fun j : ℕ => ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j) (h z))
    (hsum : Summable (fun j : ℕ =>
      (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2)) :
    IntegrableOn (fun z : ℂ => ‖h z‖ ^ 2) (Metric.ball (0 : ℂ) 1) ∧
      (Real.pi)⁻¹ *
        (∫ z in Metric.ball (0 : ℂ) 1, ‖h z‖ ^ 2 ∂volume) ≤
      ∑' j : ℕ, (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2 := by
  let D : Set ℂ := Metric.ball 0 1
  let μ : Measure ℂ := volume.restrict D
  let w : ℕ → ℝ := fun j => (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2
  let P : ℕ → ℂ → ℂ := fun N z =>
    ∑ j ∈ Finset.range N, ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j
  let e : ℕ → ℂ → ENNReal := fun N z => ENNReal.ofReal (‖P N z‖ ^ 2)
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hmeas (N : ℕ) : Measurable (e N) := by
    dsimp [e, P]
    fun_prop
  have hPcont (N : ℕ) : Continuous (P N) := by
    dsimp [P]
    fun_prop
  have hPint (N : ℕ) : Integrable (fun z => ‖P N z‖ ^ 2) μ := by
    have hcont' : Continuous (fun z : ℂ => ‖P N z‖ ^ 2) :=
      (hPcont N).norm.pow 2
    exact (hcont'.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) 1)).mono_set
      Metric.ball_subset_closedBall
  have henergy (N : ℕ) :
      (∫ z, ‖P N z‖ ^ 2 ∂μ) =
        Real.pi * ∑ j ∈ Finset.range N, w j := by
    have h := finite_derivative_modes_energy d N
    change Real.pi⁻¹ * (∫ z, ‖P N z‖ ^ 2 ∂μ) =
      ∑ j ∈ Finset.range N, w j at h
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    calc
      (∫ z, ‖P N z‖ ^ 2 ∂μ) =
          Real.pi * (Real.pi⁻¹ * (∫ z, ‖P N z‖ ^ 2 ∂μ)) := by
            field_simp
      _ = Real.pi * ∑ j ∈ Finset.range N, w j := by rw [h]
  have hlinN (N : ℕ) :
      (∫⁻ z, e N z ∂μ) =
        ENNReal.ofReal (Real.pi * ∑ j ∈ Finset.range N, w j) := by
    have hnonneg : 0 ≤ᵐ[μ] fun z => ‖P N z‖ ^ 2 :=
      Filter.Eventually.of_forall (fun z => sq_nonneg _)
    simpa only [e] using
      ((ofReal_integral_eq_lintegral_ofReal (hPint N) hnonneg).symm.trans
        (congrArg ENNReal.ofReal (henergy N)))
  have hlimN : Tendsto
      (fun N => ∫⁻ z, e N z ∂μ) atTop
      (𝓝 (ENNReal.ofReal (Real.pi * ∑' j, w j))) := by
    have hw : Summable w := hsum
    have ht : Tendsto (fun N => ∑ j ∈ Finset.range N, w j) atTop
        (𝓝 (∑' j, w j)) := hw.hasSum.tendsto_sum_nat
    have htReal : Tendsto
        (fun N => Real.pi * ∑ j ∈ Finset.range N, w j) atTop
        (𝓝 (Real.pi * ∑' j, w j)) :=
      tendsto_const_nhds.mul ht
    have ht' := ENNReal.tendsto_ofReal htReal
    simpa only [hlinN] using ht'
  have hlimPoint : ∀ᵐ z ∂μ,
      liminf (fun N => e N z) atTop = ENNReal.ofReal (‖h z‖ ^ 2) := by
    filter_upwards [ae_restrict_mem hD] with z hz
    have ht := (hpoint z hz).tendsto_sum_nat
    have htP : Tendsto (fun N => P N z) atTop (𝓝 (h z)) := by
      simpa only [P] using ht
    have htR := ((continuous_norm.pow 2).tendsto (h z)).comp htP
    have htE := ENNReal.tendsto_ofReal htR
    simpa [Function.comp_def, e] using htE.liminf_eq
  have hfatou :
      (∫⁻ z, ENNReal.ofReal (‖h z‖ ^ 2) ∂μ) ≤
        ENNReal.ofReal (Real.pi * ∑' j, w j) := by
    calc
      (∫⁻ z, ENNReal.ofReal (‖h z‖ ^ 2) ∂μ) =
          ∫⁻ z, liminf (fun N => e N z) atTop ∂μ :=
            lintegral_congr_ae (by
              filter_upwards [hlimPoint] with z hz
              exact hz.symm)
      _ ≤ liminf (fun N => ∫⁻ z, e N z ∂μ) atTop :=
        lintegral_liminf_le hmeas
      _ = ENNReal.ofReal (Real.pi * ∑' j, w j) := hlimN.liminf_eq
  have hMeas : AEStronglyMeasurable (fun z : ℂ => ‖h z‖ ^ 2) μ :=
    ((hcont.norm.pow 2).aestronglyMeasurable hD)
  have hInt : Integrable (fun z : ℂ => ‖h z‖ ^ 2) μ := by
    refine ⟨hMeas, (hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))).mpr ?_⟩
    exact lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  have hreal :
      (∫ z, ‖h z‖ ^ 2 ∂μ) ≤ Real.pi * ∑' j, w j := by
    have heq := ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))
    rw [← heq] at hfatou
    have hw0 : 0 ≤ ∑' j, w j := tsum_nonneg (fun j => by
      dsimp [w]
      positivity)
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg Real.pi_pos.le hw0)).mp hfatou
  refine ⟨hInt, ?_⟩
  have hpi : 0 < Real.pi := Real.pi_pos
  exact (inv_mul_le_iff₀ hpi).mpr hreal

end SpringerLean
