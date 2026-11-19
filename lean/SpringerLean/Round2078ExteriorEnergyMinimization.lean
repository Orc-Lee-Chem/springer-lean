import SpringerLean.Round2075ExteriorMutualEnergy
import SpringerLean.Round2076GaussianEnergyPositivity
import SpringerLean.Round2077GaussianLogKernel

open MeasureTheory Set Filter

namespace SpringerLean

/-- Twice the shifted negative logarithmic kernel. The form is
nonnegative on the common distance range `‖z-w‖ ≤ 5`, and has
the extended value infinity on the diagonal. -/
noncomputable def twiceShiftedLogKernel (p : ℂ × ℂ) : ENNReal :=
  if p.1 = p.2 then ⊤ else ENNReal.ofReal (Real.log (25 / ‖p.1-p.2‖ ^ 2))

theorem twiceShiftedLogKernel_measurable : Measurable twiceShiftedLogKernel := by
  unfold twiceShiftedLogKernel
  exact Measurable.ite (isClosed_eq continuous_fst continuous_snd).measurableSet
    measurable_const (by fun_prop)

/-- Twice the logarithmic mutual energy after shifting by `log 5`. -/
noncomputable def twiceShiftedLogEnergy (μ ν : Measure ℂ) : ENNReal :=
  ∫⁻ p, twiceShiftedLogKernel p ∂μ.prod ν

private theorem twiceShiftedLogEnergy_symm (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    twiceShiftedLogEnergy μ ν = twiceShiftedLogEnergy ν μ := by
  unfold twiceShiftedLogEnergy
  rw [← lintegral_prod_swap (μ := μ) (ν := ν) twiceShiftedLogKernel]
  apply lintegral_congr
  intro p
  by_cases hp : p.1 = p.2
  · simp [twiceShiftedLogKernel, hp]
  · simp only [twiceShiftedLogKernel, Prod.swap, hp, Ne.symm hp, ite_false,
      norm_sub_rev p.2 p.1]

private theorem ae_pair_dist_le_five (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ 2)
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 2) : ∀ᵐ p ∂μ.prod ν, ‖p.1-p.2‖ ≤ 5 := by
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_le ((continuous_fst.sub continuous_snd).norm) continuous_const).measurableSet).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact (norm_sub_le _ _).trans (by linarith)

private theorem gaussianInteraction_integrable (t : ℝ) (ht : 0 ≤ t)
    (μ ν : Measure ℂ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Integrable (fun p : ℂ × ℂ => Real.exp (-t * ‖p.1-p.2‖ ^ 2)) (μ.prod ν) := by
  apply Integrable.mono (integrable_const (1 : ℝ)) (by fun_prop)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le, norm_one, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _)

private noncomputable def gaussianEnergyDensity (μ ν : Measure ℂ) (t : ℝ) : ℝ :=
  t⁻¹ * (gaussianInteraction t μ ν - Real.exp (-25*t))

private theorem gaussianEnergyDensity_measurable (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Measurable (gaussianEnergyDensity μ ν) := by
  have h : Measurable (fun t : ℝ => gaussianInteraction t μ ν) := by
    unfold gaussianInteraction
    exact (show Measurable (fun p : ℝ × (ℂ × ℂ) =>
      Real.exp (-p.1 * ‖p.2.1-p.2.2‖ ^ 2)) by fun_prop).stronglyMeasurable.integral_prod_right'.measurable
  unfold gaussianEnergyDensity
  exact measurable_id.inv.mul (h.sub (by fun_prop))

private theorem gaussianEnergyDensity_nonneg (μ ν : Measure ℂ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : ∀ᵐ p ∂μ.prod ν, ‖p.1 - p.2‖ ≤ 5)
    (t : ℝ) (ht : 0 < t) : 0 ≤ gaussianEnergyDensity μ ν t := by
  have hle : Real.exp (-25*t) ≤ gaussianInteraction t μ ν := by
    have hm : ∀ᵐ p ∂μ.prod ν, Real.exp (-25*t) ≤ Real.exp (-t * ‖p.1-p.2‖ ^ 2) := by
      filter_upwards [h] with p hp
      have hsq : ‖p.1-p.2‖ ^ 2 ≤ 25 := by nlinarith [norm_nonneg (p.1-p.2)]
      exact Real.exp_le_exp.mpr (by nlinarith)
    simpa only [integral_const, probReal_univ, one_smul, gaussianInteraction] using
      integral_mono_ae (integrable_const (Real.exp (-25*t)))
        (gaussianInteraction_integrable t ht.le μ ν) hm
  exact mul_nonneg (inv_pos.mpr ht).le (sub_nonneg.mpr hle)

private theorem twiceShiftedLogEnergy_eq_gaussian (μ ν : Measure ℂ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ᵐ p ∂μ.prod ν, ‖p.1-p.2‖ ≤ 5) :
    twiceShiftedLogEnergy μ ν =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (gaussianEnergyDensity μ ν t) := by
  let d (p : ℂ × ℂ) := ‖p.1-p.2‖ ^ 2
  let f (p : ℂ × ℂ) (t : ℝ) := ENNReal.ofReal (gaussianLogKernel (d p) 25 t)
  have hswap : AEMeasurable (Function.uncurry f) ((μ.prod ν).prod (volume.restrict (Ioi 0))) :=
    (by unfold Function.uncurry f d gaussianLogKernel; fun_prop : Measurable _).aemeasurable
  unfold twiceShiftedLogEnergy
  calc
    _ = ∫⁻ p, ∫⁻ t in Ioi (0 : ℝ), f p t ∂volume ∂μ.prod ν := by
      apply lintegral_congr_ae
      filter_upwards [h] with p hp
      unfold f twiceShiftedLogKernel
      split_ifs with hpq
      · have hd : d p = 0 := by simp [d, hpq]
        rw [hd, lintegral_gaussianLogKernel_at_diagonal (by norm_num : (0 : ℝ) < 25)]
      · have hd0 : 0 < d p := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hpq)) _
        have hd5 : d p ≤ 25 := by dsimp [d]; nlinarith [norm_nonneg (p.1-p.2)]
        exact (lintegral_gaussianLogKernel hd0 hd5).symm
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ p, f p t ∂μ.prod ν := lintegral_lintegral_swap hswap
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hgt : 0 < t := ht
      have hi := (gaussianInteraction_integrable t hgt.le μ ν).sub
        (integrable_const (Real.exp (-25*t)))
      have he (p : ℂ × ℂ) : gaussianLogKernel (d p) 25 t =
          t⁻¹ * (Real.exp (-t * ‖p.1-p.2‖ ^ 2) - Real.exp (-25*t)) := by
        rw [gaussianLogKernel, show -d p * t = -t * ‖p.1-p.2‖ ^ 2 by dsimp [d]; ring]
      have hi' : Integrable (fun p => gaussianLogKernel (d p) 25 t) (μ.prod ν) := by
        simp_rw [he]
        exact hi.const_mul _
      have hnn : 0 ≤ᵐ[μ.prod ν] (fun p => gaussianLogKernel (d p) 25 t) := by
        filter_upwards [h] with p hp
        exact gaussianLogKernel_nonneg (by dsimp [d]; nlinarith [norm_nonneg (p.1-p.2)]) hgt
      unfold f
      rw [← ofReal_integral_eq_lintegral_ofReal hi' hnn]
      congr 1
      simp only [he, integral_const_mul,
        integral_sub (gaussianInteraction_integrable t hgt.le μ ν) (integrable_const _),
        integral_const, probReal_univ, one_smul, gaussianEnergyDensity, gaussianInteraction]

private theorem twiceShiftedLogEnergy_actual_mutual
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : exteriorOmitted F ∈ ae ν) :
    twiceShiftedLogEnergy ν (actualExteriorBoundaryProbability F) =
      ENNReal.ofReal (2 * Real.log 5) := by
  let μ := actualExteriorBoundaryProbability F
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hμ : exteriorOmitted F ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted
    F hF (exteriorOmitted_isCompact F hF).isClosed
  have hν2 : ∀ᵐ z ∂ν, ‖z‖ ≤ 2 := by
    filter_upwards [hν] with z hz
    exact exteriorOmitted_norm_le_two F hF hz
  have hμ2 : ∀ᵐ z ∂μ, ‖z‖ ≤ 2 := by
    filter_upwards [hμ] with z hz
    exact exteriorOmitted_norm_le_two F hF hz
  have hdist := ae_pair_dist_le_five ν μ hν2 hμ2
  obtain ⟨hne, hi, hz⟩ := actualExteriorBoundaryProbability_mutual_log_energy F hF ν hν
  let L (p : ℂ × ℂ) := 2 * Real.log 5 - 2 * Real.log ‖p.2-p.1‖
  have hn : 0 ≤ᵐ[ν.prod μ] L := by
    filter_upwards [hne, hdist] with p hp hδ
    have hδ' : ‖p.2-p.1‖ ≤ 5 := by rwa [norm_sub_rev]
    have hleft := Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hp)) hδ'
    dsimp [L]
    linarith
  have hLi : Integrable L (ν.prod μ) := (integrable_const _).sub (hi.const_mul _)
  unfold twiceShiftedLogEnergy
  calc
    _ = ∫⁻ p, ENNReal.ofReal (L p) ∂ν.prod μ := by
      apply lintegral_congr_ae
      filter_upwards [hne] with p hp
      have hd : 0 < ‖p.1-p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp.symm)
      simp only [twiceShiftedLogKernel, hp.symm, if_false, L, norm_sub_rev p.2 p.1]
      congr 1
      rw [Real.log_div (by norm_num) (pow_ne_zero _ hd.ne'), Real.log_pow,
        show (25 : ℝ) = 5^2 by norm_num, Real.log_pow]
      norm_num
    _ = ENNReal.ofReal (∫ p, L p ∂ν.prod μ) :=
      (ofReal_integral_eq_lintegral_ofReal hLi hn).symm
    _ = _ := by
      congr 1
      have hm : Integrable (fun p : ℂ × ℂ => 2 * Real.log ‖p.2-p.1‖) (ν.prod μ) :=
        hi.const_mul _
      dsimp only [L]
      rw [integral_sub (integrable_const _) hm, integral_const,
        probReal_univ, one_smul, integral_const_mul]
      change 2 * Real.log 5 - 2 * (∫ p : ℂ × ℂ, Real.log ‖p.2-p.1‖ ∂ν.prod
        (actualExteriorBoundaryProbability F)) = _
      rw [hz, mul_zero, sub_zero]

/-- The actual radial law minimizes the negative logarithmic energy of
probabilities carried by its omitted set. In the shifted energy
normalization the minimum is `2 log 5`, corresponding to unshifted
energy zero. -/
theorem actualExteriorBoundaryProbability_minimizes_log_energy
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : exteriorOmitted F ∈ ae ν) :
    twiceShiftedLogEnergy (actualExteriorBoundaryProbability F)
      (actualExteriorBoundaryProbability F) = ENNReal.ofReal (2 * Real.log 5) ∧
    twiceShiftedLogEnergy (actualExteriorBoundaryProbability F)
      (actualExteriorBoundaryProbability F) ≤ twiceShiftedLogEnergy ν ν := by
  let μ := actualExteriorBoundaryProbability F
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hμ : exteriorOmitted F ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted
    F hF (exteriorOmitted_isCompact F hF).isClosed
  have hactual := twiceShiftedLogEnergy_actual_mutual F hF μ hμ
  have hcross := twiceShiftedLogEnergy_actual_mutual F hF ν hν
  have hcross' := (twiceShiftedLogEnergy_symm μ ν).trans hcross
  refine ⟨hactual, ?_⟩
  have hμ2 : ∀ᵐ z ∂μ, ‖z‖ ≤ 2 := by
    filter_upwards [hμ] with z hz
    exact exteriorOmitted_norm_le_two F hF hz
  have hν2 : ∀ᵐ z ∂ν, ‖z‖ ≤ 2 := by
    filter_upwards [hν] with z hz
    exact exteriorOmitted_norm_le_two F hF hz
  have hμμ := ae_pair_dist_le_five μ μ hμ2 hμ2
  have hνν := ae_pair_dist_le_five ν ν hν2 hν2
  have hμν := ae_pair_dist_le_five μ ν hμ2 hν2
  have hνμ := ae_pair_dist_le_five ν μ hν2 hμ2
  have hineq :
      twiceShiftedLogEnergy μ ν + twiceShiftedLogEnergy ν μ ≤
        twiceShiftedLogEnergy μ μ + twiceShiftedLogEnergy ν ν := by
    rw [twiceShiftedLogEnergy_eq_gaussian μ ν hμν, twiceShiftedLogEnergy_eq_gaussian ν μ hνμ,
      twiceShiftedLogEnergy_eq_gaussian μ μ hμμ, twiceShiftedLogEnergy_eq_gaussian ν ν hνν,
      ← lintegral_add_left (gaussianEnergyDensity_measurable μ ν).ennreal_ofReal,
      ← lintegral_add_left (gaussianEnergyDensity_measurable μ μ).ennreal_ofReal]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [← ENNReal.ofReal_add (gaussianEnergyDensity_nonneg μ ν hμν t ht)
      (gaussianEnergyDensity_nonneg ν μ hνμ t ht),
      ← ENNReal.ofReal_add (gaussianEnergyDensity_nonneg μ μ hμμ t ht)
        (gaussianEnergyDensity_nonneg ν ν hνν t ht)]
    apply ENNReal.ofReal_le_ofReal
    unfold gaussianEnergyDensity
    have h0 := gaussianInteraction_difference_nonneg t ht.le μ ν
    have hpoint : gaussianInteraction t μ ν + gaussianInteraction t ν μ ≤
        gaussianInteraction t μ μ + gaussianInteraction t ν ν := by linarith
    have hh := mul_le_mul_of_nonneg_left hpoint (inv_pos.mpr ht).le
    nlinarith only [hh]
  rw [hactual, hcross, hcross'] at hineq
  rw [hactual]
  exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp hineq

/-- Equality in the energy minimum determines the actual radial law.
The zero Gaussian energy at one positive scale determines the
probability by its characteristic function. -/
theorem actualExteriorBoundaryProbability_unique_log_energy_minimizer
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ν : Measure ℂ) [IsProbabilityMeasure ν] (hν : exteriorOmitted F ∈ ae ν)
    (heq : twiceShiftedLogEnergy ν ν = ENNReal.ofReal (2 * Real.log 5)) :
    ν = actualExteriorBoundaryProbability F := by
  let μ := actualExteriorBoundaryProbability F
  let S := volume.restrict (Ioi (0 : ℝ))
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hμ : exteriorOmitted F ∈ ae μ := actualExteriorBoundaryProbability_ae_mem_omitted
    F hF (exteriorOmitted_isCompact F hF).isClosed
  have hactual := twiceShiftedLogEnergy_actual_mutual F hF μ hμ
  have hcross := twiceShiftedLogEnergy_actual_mutual F hF ν hν
  have hcross' := (twiceShiftedLogEnergy_symm μ ν).trans hcross
  have hμ2 : ∀ᵐ z ∂μ, ‖z‖ ≤ 2 := by
    filter_upwards [hμ] with z hz
    exact exteriorOmitted_norm_le_two F hF hz
  have hν2 : ∀ᵐ z ∂ν, ‖z‖ ≤ 2 := by
    filter_upwards [hν] with z hz
    exact exteriorOmitted_norm_le_two F hF hz
  have hμμ := ae_pair_dist_le_five μ μ hμ2 hμ2
  have hνν := ae_pair_dist_le_five ν ν hν2 hν2
  have hμν := ae_pair_dist_le_five μ ν hμ2 hν2
  have hνμ := ae_pair_dist_le_five ν μ hν2 hμ2
  let Q (t : ℝ) := gaussianEnergyDensity μ μ t + gaussianEnergyDensity ν ν t -
    gaussianEnergyDensity μ ν t - gaussianEnergyDensity ν μ t
  have hQ (t : ℝ) :
      Q t = t⁻¹ * (gaussianInteraction t μ μ + gaussianInteraction t ν ν -
        gaussianInteraction t μ ν - gaussianInteraction t ν μ) := by
    dsimp [Q, gaussianEnergyDensity]
    ring
  have hQ0 (t : ℝ) (ht : 0 < t) : 0 ≤ Q t := by
    rw [hQ]
    exact mul_nonneg (inv_pos.mpr ht).le (gaussianInteraction_difference_nonneg t ht.le μ ν)
  have hmeas : Measurable (fun t => ENNReal.ofReal (Q t)) := by
    unfold Q
    exact ((((gaussianEnergyDensity_measurable μ μ).add (gaussianEnergyDensity_measurable ν ν)).sub
      (gaussianEnergyDensity_measurable μ ν)).sub
      (gaussianEnergyDensity_measurable ν μ)).ennreal_ofReal
  have htotal : twiceShiftedLogEnergy μ μ + twiceShiftedLogEnergy ν ν =
      twiceShiftedLogEnergy μ ν + twiceShiftedLogEnergy ν μ +
      ∫⁻ t, ENNReal.ofReal (Q t) ∂S := by
    have hsum : Measurable (fun t => ENNReal.ofReal (gaussianEnergyDensity μ ν t) +
        ENNReal.ofReal (gaussianEnergyDensity ν μ t)) :=
      (gaussianEnergyDensity_measurable μ ν).ennreal_ofReal.add
        (gaussianEnergyDensity_measurable ν μ).ennreal_ofReal
    rw [twiceShiftedLogEnergy_eq_gaussian μ μ hμμ, twiceShiftedLogEnergy_eq_gaussian ν ν hνν,
      twiceShiftedLogEnergy_eq_gaussian μ ν hμν, twiceShiftedLogEnergy_eq_gaussian ν μ hνμ,
      ← lintegral_add_left (gaussianEnergyDensity_measurable μ μ).ennreal_ofReal,
      ← lintegral_add_left (gaussianEnergyDensity_measurable μ ν).ennreal_ofReal]
    rw [← lintegral_add_left (μ := S) hsum (fun t => ENNReal.ofReal (Q t))]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    rw [← ENNReal.ofReal_add (gaussianEnergyDensity_nonneg μ μ hμμ t ht)
      (gaussianEnergyDensity_nonneg ν ν hνν t ht),
      ← ENNReal.ofReal_add (gaussianEnergyDensity_nonneg μ ν hμν t ht)
        (gaussianEnergyDensity_nonneg ν μ hνμ t ht),
      ← ENNReal.ofReal_add (add_nonneg (gaussianEnergyDensity_nonneg μ ν hμν t ht)
        (gaussianEnergyDensity_nonneg ν μ hνμ t ht)) (hQ0 t ht)]
    congr 1
    dsimp [Q]
    ring
  rw [hactual, heq, hcross', hcross] at htotal
  have hfin : ENNReal.ofReal (2 * Real.log 5) + ENNReal.ofReal (2 * Real.log 5) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hzero : (∫⁻ t, ENNReal.ofReal (Q t) ∂S) = 0 := by
    apply (ENNReal.add_right_inj hfin).mp
    simpa only [add_zero] using htotal.symm
  have hae := (lintegral_eq_zero_iff hmeas).mp hzero
  have hS : NeZero S := ⟨by
    intro h
    have hz : S univ = 0 := by rw [h]; simp
    simpa [S, Real.volume_Ioi] using hz⟩
  obtain ⟨t, ht, hz⟩ := ((ae_restrict_mem (μ := volume) (s := Ioi (0 : ℝ))
    measurableSet_Ioi).and hae).exists
  have ht0 : 0 < t := ht
  have hzeroQ : Q t = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (hQ0 t ht0)
  rw [hQ] at hzeroQ
  have he := (mul_eq_zero.mp hzeroQ).resolve_left (inv_pos.mpr ht0).ne'
  exact (eq_of_gaussianInteraction_difference_eq_zero t ht0 μ ν he).symm

end SpringerLean
