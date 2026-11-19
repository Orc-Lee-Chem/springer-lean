import SpringerLean.Round37KernelLevels

open MeasureTheory Set Metric Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- The actual regularized boundary projection has a bound independent of
angle, as required for the finite-measure layer-cake theorem. -/
theorem regularExterior_projected_angle_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ θ : ℝ,
        |(conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound_closedDisk F hc
  refine ⟨C, hC0, ?_⟩
  intro θ
  let ζ := circleMap 0 1 θ
  have hz : ‖ζ‖ = 1 := by simpa [ζ] using norm_circleMap_zero 1 θ
  have hG : ‖rescaleExterior s F ζ‖ ≤ C := by
    rw [← regularHarmonic_unitCircle_eq_actual F hs0 hz]
    exact hC s hs0 hs1 ζ hz.le
  have hξc : ‖conj ξ‖ = 1 := by simpa using hξ
  calc
    |(conj ξ * rescaleExterior s F ζ).re| ≤
      ‖conj ξ * rescaleExterior s F ζ‖ := Complex.abs_re_le_norm _
    _ = ‖conj ξ‖ * ‖rescaleExterior s F ζ‖ := norm_mul _ _
    _ = ‖rescaleExterior s F ζ‖ := by rw [hξc, one_mul]
    _ ≤ C := hG

/-- Centered Poisson weight is continuous as an angular function. -/
theorem centeredPoisson_weight_continuous
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous (fun θ : ℝ => poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)) := by
  have hd : ∀ θ : ℝ, 1+r^2-2*r*Real.cos θ ≠ 0 :=
    fun θ => (centeredPoissonDenominator_pos hr0 hr1 θ).ne'
  have hc : Continuous (fun θ : ℝ =>
      (1-r^2)/(1+r^2-2*r*Real.cos θ)) := by
    exact continuous_const.div (by fun_prop) hd
  exact hc.congr (fun θ => (poissonKernel_centered_cosine_formula hr0.le hr1 θ).symm)


/-- The actual-minus-comparison projected boundary has a nonpositive
Poisson-weighted integral at a real observation radius. -/
theorem regularExterior_centered_poisson_projection_difference_nonpos
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (∫ θ : ℝ,
      ((conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re -
        2 * (circleMap 0 1 θ).re) *
        poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)
      ∂(volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) ≤ 0 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ := fun θ =>
    (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
  let g : ℝ → ℝ := fun θ => 2 * (circleMap 0 1 θ).re
  let h : ℝ → ℝ := fun θ => f θ - g θ
  let w : ℝ → ℝ := fun θ => poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_projected_angle_bounded F hc hs0 hs1 ξ hξ
  have hfCont : Continuous f := by
    exact Complex.continuous_re.comp (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
  have hgCont : Continuous g := by fun_prop
  have hwCont : Continuous w := centeredPoisson_weight_continuous hr0 hr1
  have hhMeas : Measurable h := hfCont.measurable.sub hgCont.measurable
  have hgBound (θ : ℝ) : |g θ| ≤ 2 := by
    change |2 * (circleMap 0 1 θ).re| ≤ 2
    rw [circleMap_zero_re]
    simp only [one_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [Real.abs_cos_le_one θ]
  have hB0 : 0 ≤ C + 2 := by linarith
  have hBound (θ : ℝ) : |h θ| ≤ C + 2 := by
    calc
      |h θ| ≤ |f θ| + |g θ| := abs_sub _ _
      _ ≤ C + 2 := add_le_add (hC θ) (hgBound θ)
  have hfInt : Integrable f μ := by
    apply Integrable.mono' (g := fun _ : ℝ => C) (integrable_const C)
      hfCont.measurable.aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs] using hC θ
  have hgInt : Integrable g μ := by
    apply Integrable.mono' (g := fun _ : ℝ => (2:ℝ)) (integrable_const 2)
      hgCont.measurable.aestronglyMeasurable
    filter_upwards [] with θ
    simpa only [Real.norm_eq_abs] using hgBound θ
  have hlevels (t : ℝ) (ht : 0 < t) (_ : t ≤ (1-r^2)/(1-r)^2) :
      (∫ θ in {θ | t ≤ w θ}, h θ ∂μ) ≤ 0 := by
    have hbase := regularExterior_projected_poisson_level_le_comparator
      F hc hs0 hs1 ξ hξ hr0 hr1 ht
    change (∫ θ in {θ | t ≤ w θ}, f θ ∂μ) ≤
      (∫ θ in {θ | t ≤ w θ}, g θ ∂μ) at hbase
    change (∫ θ in {θ | t ≤ w θ}, f θ - g θ ∂μ) ≤ 0
    rw [integral_sub hfInt.integrableOn hgInt.integrableOn]
    exact sub_nonpos.mpr hbase
  have hw0 (θ : ℝ) : 0 ≤ w θ :=
    (centeredPoisson_weight_bounds hr0 hr1 θ).1
  have hwM (θ : ℝ) : w θ ≤ (1-r^2)/(1-r)^2 :=
    (centeredPoisson_weight_bounds hr0 hr1 θ).2
  exact bounded_weighted_integral_nonpos_of_levels
    μ h w hhMeas hwCont.measurable (C+2) ((1-r^2)/(1-r)^2)
    hB0 hBound hw0 hwM hlevels

/-- Real circle average in the restricted one-turn Lebesgue normalization. -/
theorem circleAverage_eq_restrictedAngularIntegral (q : ℂ → ℝ) :
    Real.circleAverage q 0 1 =
      (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ, q (circleMap 0 1 θ)
          ∂(volume.restrict (Ioc (0:ℝ) (2 * Real.pi)))) := by
  rw [Real.circleAverage_def,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  rfl

/-- The centered Poisson average of the actual regularized boundary
projection is bounded by the matching Poisson average of 2 cos θ. -/
theorem regularExterior_centered_poisson_projection_circleAverage_le_comparator
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ : ℂ =>
      poissonKernel 0 (r : ℂ) ζ * (conj ξ * rescaleExterior s F ζ).re) 0 1 ≤
    Real.circleAverage (fun ζ : ℂ =>
      poissonKernel 0 (r : ℂ) ζ * (2 * ζ.re)) 0 1 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0:ℝ) (2 * Real.pi))
  let P : ℝ → ℝ := fun θ => poissonKernel 0 (r : ℂ) (circleMap 0 1 θ)
  let f : ℝ → ℝ := fun θ => (conj ξ * rescaleExterior s F (circleMap 0 1 θ)).re
  let g : ℝ → ℝ := fun θ => 2 * (circleMap 0 1 θ).re
  have hpc : Continuous P := centeredPoisson_weight_continuous hr0 hr1
  have hfc : Continuous f :=
    Complex.continuous_re.comp (regularExterior_rotated_angle_continuous F hc hs0 hs1 ξ)
  have hgc : Continuous g := by fun_prop
  have hfi : Integrable (fun θ => P θ * f θ) μ := by
    change IntegrableOn (fun θ => P θ * f θ) (Ioc 0 (2 * Real.pi))
    exact ((hpc.mul hfc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hgi : Integrable (fun θ => P θ * g θ) μ := by
    change IntegrableOn (fun θ => P θ * g θ) (Ioc 0 (2 * Real.pi))
    exact ((hpc.mul hgc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have hraw := regularExterior_centered_poisson_projection_difference_nonpos
    F hc hs0 hs1 ξ hξ hr0 hr1
  change (∫ θ, (f θ - g θ) * P θ ∂μ) ≤ 0 at hraw
  have hsplit : (∫ θ, (f θ-g θ) * P θ ∂μ) =
      (∫ θ, P θ*f θ ∂μ) - (∫ θ, P θ*g θ ∂μ) := by
    calc
      _ = ∫ θ, P θ*f θ - P θ*g θ ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with θ
        ring
      _ = _ := integral_sub hfi hgi
  rw [hsplit] at hraw
  rw [circleAverage_eq_restrictedAngularIntegral,
    circleAverage_eq_restrictedAngularIntegral]
  apply mul_le_mul_of_nonneg_left (sub_nonpos.mp hraw)
  positivity

/-- The sharp centered interior projection constant for every actual
regularized exterior map. -/
theorem regularExterior_centered_poisson_projection_circleAverage_le_two_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ : ℂ =>
      poissonKernel 0 (r : ℂ) ζ * (conj ξ * rescaleExterior s F ζ).re) 0 1 ≤
      2 * r := by
  calc
    _ ≤ Real.circleAverage (fun ζ : ℂ =>
        poissonKernel 0 (r : ℂ) ζ * (2 * ζ.re)) 0 1 :=
      regularExterior_centered_poisson_projection_circleAverage_le_comparator
        F hc hs0 hs1 ξ hξ hr0 hr1
    _ = 2 * r := poissonKernel_comparator_centered hr0.le hr1

/-- Directional real projection of the actual Poisson representation,
for an arbitrary interior observation point. -/
theorem regularHarmonic_projected_poisson_circleAverage
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Real.circleAverage (fun ζ : ℂ =>
      poissonKernel 0 z ζ * (conj ξ * rescaleExterior s F ζ).re) 0 1 =
      (conj ξ * regularHarmonic s F z).re := by
  have hnot : z ∉ sphere (0 : ℂ) 1 := by
    intro hzs
    have hlt : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    have heq : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hzs
    linarith
  have hkernel : ContinuousOn (poissonKernel 0 z) (sphere (0 : ℂ) 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simpa only [abs_one] using
      (Complex.continuous_re.comp_continuousOn
        (continuousOn_herglotzRieszKernel_sphere
          (c := (0 : ℂ)) (w := z) (R := (1 : ℝ))
          (by simpa only [abs_one] using hnot)))
  have hF : ∀ u ∈ exteriorDisk, AnalyticAt ℂ F u :=
    fun u hu => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hu)
  have hGcont : ContinuousOn (rescaleExterior s F) (sphere (0 : ℂ) 1) := by
    intro u hu
    have hunorm : ‖u‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hu
    have hext : u ∈ exteriorAbove s := by
      change s < ‖u‖
      rw [hunorm]
      exact hs1
    exact (rescaleExterior_analyticAt hs0 hF hext).continuousAt.continuousWithinAt
  have hrot : ContinuousOn (fun u : ℂ => conj ξ * rescaleExterior s F u)
      (sphere (0 : ℂ) 1) := continuousOn_const.mul hGcont
  have hci : CircleIntegrable
      (fun u : ℂ => (poissonKernel 0 z u) • (conj ξ * rescaleExterior s F u))
      0 1 := (hkernel.smul hrot).circleIntegrable (by norm_num)
  have hre := Complex.reCLM.circleAverage_comp_comm hci
  have hre' : Real.circleAverage (fun u : ℂ =>
      poissonKernel 0 z u * (conj ξ * rescaleExterior s F u).re) 0 1 =
      (Real.circleAverage (fun u : ℂ =>
        (poissonKernel 0 z u) • (conj ξ * rescaleExterior s F u)) 0 1).re := by
    simpa [Function.comp_def, Complex.reCLM_apply, Complex.real_smul] using hre
  rw [hre']
  have hsmul : Real.circleAverage (fun u : ℂ =>
      (poissonKernel 0 z u) • (conj ξ * rescaleExterior s F u)) 0 1 =
      conj ξ * Real.circleAverage (fun u : ℂ =>
        (poissonKernel 0 z u) • rescaleExterior s F u) 0 1 := by
    calc
      _ = Real.circleAverage (fun u : ℂ =>
          (conj ξ) • ((poissonKernel 0 z u) • rescaleExterior s F u)) 0 1 := by
        congr 1
        funext u
        simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      _ = (conj ξ) • Real.circleAverage (fun u : ℂ =>
          (poissonKernel 0 z u) • rescaleExterior s F u) 0 1 :=
        Real.circleAverage_fun_smul
      _ = _ := by simp [smul_eq_mul]
  rw [hsmul, regularHarmonic_poisson_actualBoundary F hc hs0 hs1 hz]

/-- Sharp actual directional bound for the regularized filling on the
positive real radius. -/
theorem regularHarmonic_centered_projection_le_two_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (conj ξ * regularHarmonic s F (r : ℂ)).re ≤ 2 * r := by
  have hz : (r : ℂ) ∈ ball (0 : ℂ) 1 := by
    simp only [mem_ball, dist_zero_right]
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1
  calc
    _ = Real.circleAverage (fun ζ : ℂ =>
        poissonKernel 0 (r : ℂ) ζ *
          (conj ξ * rescaleExterior s F ζ).re) 0 1 :=
      (regularHarmonic_projected_poisson_circleAverage F hc hs0 hs1 ξ hz).symm
    _ ≤ 2 * r :=
      regularExterior_centered_poisson_projection_circleAverage_le_two_radius
        F hc hs0 hs1 ξ hξ hr0 hr1

/-- A complex norm is attained by projection onto its own unit direction. -/
theorem complex_norm_le_of_all_unit_projections
    (w : ℂ) (M : ℝ)
    (h : ∀ ξ : ℂ, ‖ξ‖ = 1 → (conj ξ * w).re ≤ M) :
    ‖w‖ ≤ M := by
  by_cases hw : w = 0
  · subst w
    simpa using h 1 (by norm_num)
  let ξ : ℂ := w / (‖w‖ : ℂ)
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hnp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hn)
  have hξ : ‖ξ‖ = 1 := by
    simp [ξ, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnp, hn]
  have hdir : conj ξ * w = (‖w‖ : ℂ) := by
    dsimp [ξ]
    rw [map_div₀, Complex.conj_ofReal]
    calc
      conj w / (‖w‖ : ℂ) * w = (w * conj w) / (‖w‖ : ℂ) := by ring
      _ = (((‖w‖ ^ 2 : ℝ) : ℂ)) / (‖w‖ : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      _ = (‖w‖ : ℂ) := by
        field_simp [hn]
        norm_cast
  have hh := h ξ hξ
  rw [hdir] at hh
  simpa only [Complex.ofReal_re] using hh

/-- Every actual regularized filling obeys the sharp factor 2 on the
positive real radius. -/
theorem regularHarmonic_centered_norm_le_two_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖regularHarmonic s F (r : ℂ)‖ ≤ 2 * r := by
  apply complex_norm_le_of_all_unit_projections
  intro ξ hξ
  exact regularHarmonic_centered_projection_le_two_radius
    F hc hs0 hs1 ξ hξ hr0 hr1

/-- The original, unregularized filling has the sharp factor 2 on every
positive real radius. -/
theorem actualHarmonic_centered_norm_le_two_radius
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖actualHarmonic F (r : ℂ)‖ ≤ 2 * r := by
  have hz : ‖(r : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hs : Tendsto omittedScaleSeq atTop (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨omittedScaleSeq_tendsto_one,
      Filter.Eventually.of_forall omittedScaleSeq_lt_one⟩
  have hreg : Tendsto (fun n : ℕ =>
      regularHarmonic (omittedScaleSeq n) F (r : ℂ)) atTop
      (𝓝 (actualHarmonic F (r : ℂ))) := by
    simpa only [actualHarmonic, Function.comp_def] using
      (regularHarmonic_tendsto F hc hz).comp hs
  have hnorm : Tendsto (fun n : ℕ =>
      ‖regularHarmonic (omittedScaleSeq n) F (r : ℂ)‖) atTop
      (𝓝 ‖actualHarmonic F (r : ℂ)‖) :=
    (continuous_norm.tendsto _).comp hreg
  exact le_of_tendsto_of_tendsto hnorm tendsto_const_nhds
    (Filter.Eventually.of_forall (fun n =>
      regularHarmonic_centered_norm_le_two_radius
        F hc (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) hr0 hr1))
end SpringerLean