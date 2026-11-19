import SpringerLean.Round2009OddStarUniformDerivativeBound

open MeasureTheory

namespace SpringerLean
open scoped RealInnerProductSpace
open scoped Topology

theorem oddStarOppositeTipLogDistance_joint_continuousAt
    (m : ℕ) (hm : 3 ≤ m) (t θ : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane)
    (hdist : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => oddStarOppositeTipLogDistance m p.2 p.1)
      (t, θ) := by
  have hZ := oddStarMovingBoundaryPoint_joint_continuousAt_general
    m hm t θ hden hslit
  have hR : ContinuousAt (oddStarTipRadius m) t :=
    (oddStarTipRadius_differentiableAt m t ht).continuousAt
  have hRjoint : ContinuousAt
      (fun p : ℝ × ℝ => oddStarTipRadius m p.1) (t, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.1) (t, θ) := continuousAt_fst
    exact hR.comp hp
  have hnorm :
      ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdist
  change ContinuousAt (fun p : ℝ × ℝ =>
    Real.log ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m p.2) p.2 p.1 -
      (oddStarTipRadius m p.1 : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖)
      (t, θ)
  fun_prop (discharger := assumption)

theorem oddStarOppositeTipLogDistance_continuousOn_angle
    (m : ℕ) (hm : 3 ≤ m) (t : ℝ) (ht : |t| < 1)
    (hreg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      oddStarBoundaryDenominator
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0 ∧
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane ∧
      oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0) :
    ContinuousOn (fun θ => oddStarOppositeTipLogDistance m θ t)
      (Set.Icc 0 (2 * Real.pi)) := by
  intro θ hθ
  obtain ⟨hden, hslit, hdist⟩ := hreg θ hθ
  have h := oddStarOppositeTipLogDistance_joint_continuousAt
    m hm t θ ht hden hslit hdist
  have hp : ContinuousAt (fun x : ℝ => (t, x)) θ := by fun_prop
  exact (h.comp hp).continuousWithinAt

theorem oddStarOppositeTipLogSlope_continuousOn_angle
    (m : ℕ) (hm : 3 ≤ m) (t : ℝ) (ht : |t| < 1)
    (hreg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      oddStarBoundaryDenominator
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0 ∧
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane ∧
      oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0) :
    ContinuousOn (fun θ => oddStarOppositeTipLogSlope m θ t)
      (Set.Icc 0 (2 * Real.pi)) := by
  intro θ hθ
  obtain ⟨hden, hslit, hdist⟩ := hreg θ hθ
  have h := oddStarOppositeTipLogSlope_joint_continuousAt
    m hm t θ ht hden hslit hdist
  have hp : ContinuousAt (fun x : ℝ => (t, x)) θ := by fun_prop
  exact (h.comp hp).continuousWithinAt

theorem oddStarOppositeTipLogDistance_measurable_angle
    (m : ℕ) (t : ℝ) :
    Measurable (fun θ => oddStarOppositeTipLogDistance m θ t) := by
  unfold oddStarOppositeTipLogDistance oddStarMovingBoundaryPoint
    oddStarBoundaryFactor oddStarBoundaryRadius
  fun_prop

theorem oddStarOppositeTipLogDistance_integral_hasDerivAt_zero
    (m : ℕ) (hm : 3 ≤ m) :
    HasDerivAt
      (fun t : ℝ => ∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarOppositeTipLogDistance m θ t)
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarOppositeTipLogSlope m θ 0) 0 := by
  obtain ⟨ε, M, hε, hbound⟩ :=
    oddStarOppositeTipLogSlope_uniform_bound m hm
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  have h0 : (0 : ℝ) ∈ U := mem_of_mem_nhds hU
  have hRpos : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hreg0 (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
      oddStarBoundaryDenominator
        (Complex.exp ((θ : ℂ) * Complex.I)) 0 ≠ 0 ∧
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) 0 ∈ Complex.slitPlane ∧
      oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 -
        (oddStarTipRadius m 0 : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0 := by
    have hp := hreg 0 h0 θ hθ
    refine ⟨hp.2.2, hp.2.1, ?_⟩
    intro heq
    rw [heq, norm_zero] at hp
    linarith [hp.1]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hsub : Set.uIoc (0 : ℝ) (2 * Real.pi) ⊆
      Set.Icc (0 : ℝ) (2 * Real.pi) := by
    intro θ hθ
    rw [Set.uIoc_of_le hpi] at hθ
    exact ⟨hθ.1.le, hθ.2⟩
  have hcontF := oddStarOppositeTipLogDistance_continuousOn_angle
    m hm 0 (by norm_num) hreg0
  have hcontSlope := oddStarOppositeTipLogSlope_continuousOn_angle
    m hm 0 (by norm_num) hreg0
  have hs : Set.Icc (-ε) ε ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by linarith) hε
  have hF_meas : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      AEStronglyMeasurable
        (fun θ => oddStarOppositeTipLogDistance m θ t)
        (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    filter_upwards [] with t
    exact (oddStarOppositeTipLogDistance_measurable_angle m t).aestronglyMeasurable
  have hF_int : IntervalIntegrable
      (fun θ => oddStarOppositeTipLogDistance m θ 0)
      volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc hpi hcontF
  have hF'_meas : AEStronglyMeasurable
      (fun θ => oddStarOppositeTipLogSlope m θ 0)
      (volume.restrict (Set.uIoc 0 (2 * Real.pi))) :=
    (hcontSlope.mono hsub).aestronglyMeasurable measurableSet_uIoc
  have h_bound : ∀ᵐ θ : ℝ ∂volume,
      θ ∈ Set.uIoc 0 (2 * Real.pi) →
        ∀ t ∈ Set.Icc (-ε) ε,
          ‖oddStarOppositeTipLogSlope m θ t‖ ≤ M := by
    filter_upwards [] with θ hθ t ht
    simpa [Real.norm_eq_abs] using (hbound t ht θ (hsub hθ)).2
  have h_diff : ∀ᵐ θ : ℝ ∂volume,
      θ ∈ Set.uIoc 0 (2 * Real.pi) →
        ∀ t ∈ Set.Icc (-ε) ε,
          HasDerivAt (oddStarOppositeTipLogDistance m θ)
            (oddStarOppositeTipLogSlope m θ t) t := by
    filter_upwards [] with θ hθ t ht
    exact (hbound t ht θ (hsub hθ)).1
  have hbound_int : IntervalIntegrable (fun _ : ℝ => M)
      volume 0 (2 * Real.pi) := intervalIntegrable_const
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

theorem oddStarOppositeTipLogSlope_zero_eq_variation
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    oddStarOppositeTipLogSlope m θ 0 = oddStarPointwiseVariation m θ := by
  obtain ⟨ε, M, hε, hbound⟩ :=
    oddStarOppositeTipLogSlope_uniform_bound m hm
  have h0 : (0 : ℝ) ∈ Set.Icc (-ε) ε := by
    constructor <;> linarith
  exact (hbound 0 h0 θ hθ).1.unique
    (oddStarOppositeTipLogDistance_hasDerivAt_pointwiseVariation m hm θ)

theorem oddStarOppositeTipLogDistance_integral_deriv_strict_pos
    (m : ℕ) (hm : 3 ≤ m) :
    0 < deriv (fun t : ℝ => ∫ θ in (0 : ℝ)..2 * Real.pi,
      oddStarOppositeTipLogDistance m θ t) 0 := by
  have h := oddStarOppositeTipLogDistance_integral_hasDerivAt_zero m hm
  rw [h.deriv]
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have heq : (∫ θ in (0 : ℝ)..2 * Real.pi,
      oddStarOppositeTipLogSlope m θ 0) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        oddStarPointwiseVariation m θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact oddStarOppositeTipLogSlope_zero_eq_variation m hm θ
      (by simpa only [Set.uIcc_of_le hpi] using hθ)
  rw [heq]
  exact oddStarPointwiseVariation_integral_pos m hm

end SpringerLean
