import SpringerLean.Round2008OddStarGeneralParameterDerivative

namespace SpringerLean
open scoped RealInnerProductSpace
open scoped Topology

theorem oddStarAlpha_joint_continuousAt
    (t θ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ => oddStarAlpha p.1) (t, θ) := by
  unfold oddStarAlpha
  fun_prop

theorem oddStarAlphaSlope_joint_continuousAt
    (t θ : ℝ) (ht : |t| < 1) :
    ContinuousAt (fun p : ℝ × ℝ => oddStarAlphaSlope p.1) (t, θ) := by
  have hbase : 0 < 1 - t ^ 2 := by
    have hlt := abs_lt.mp ht
    nlinarith
  have hden : 2 * Real.sqrt (1 - t ^ 2) ≠ 0 := by
    positivity
  have hreal : ContinuousAt (fun p : ℝ × ℝ =>
      (-2 * p.1) / (2 * Real.sqrt (1 - p.1 ^ 2))) (t, θ) := by
    fun_prop (discharger := assumption)
  have hcast : ContinuousAt (fun p : ℝ × ℝ =>
      (((-2 * p.1) / (2 * Real.sqrt (1 - p.1 ^ 2))) : ℂ)) (t, θ) := by
    convert Complex.continuous_ofReal.continuousAt.comp hreal using 1
    funext p
    simp
  change ContinuousAt (fun p : ℝ × ℝ =>
    (((-2 * p.1) / (2 * Real.sqrt (1 - p.1 ^ 2))) : ℂ) - Complex.I) (t, θ)
  fun_prop

theorem oddStarBoundaryDenominator_joint_continuousAt
    (t θ : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ =>
      oddStarBoundaryDenominator
        (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1) (t, θ) := by
  unfold oddStarBoundaryDenominator oddStarAlpha
  fun_prop

theorem oddStarBoundaryFactor_joint_continuousAt
    (t θ : ℝ)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ =>
      oddStarBoundaryFactor
        (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1) (t, θ) := by
  have hden' :
      ((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) *
        Complex.exp ((θ : ℂ) * Complex.I) - (t : ℂ) * Complex.I ≠ 0 :=
    hden
  unfold oddStarBoundaryFactor
  fun_prop (discharger := assumption)

theorem oddStarBoundaryFactorSlope_joint_continuousAt
    (t θ : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ =>
      oddStarBoundaryFactorSlope
        (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1) (t, θ) := by
  have hα := oddStarAlpha_joint_continuousAt t θ
  have hα' := oddStarAlphaSlope_joint_continuousAt t θ ht
  have hdenjoint := oddStarBoundaryDenominator_joint_continuousAt t θ
  have hθC : ContinuousAt (fun p : ℝ × ℝ => (p.2 : ℂ)) (t, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.2) (t, θ) := continuousAt_snd
    convert Complex.continuous_ofReal.continuousAt.comp hp using 1
    funext p
    rfl
  have hζ : ContinuousAt
      (fun p : ℝ × ℝ => Complex.exp ((p.2 : ℂ) * Complex.I)) (t, θ) := by
    fun_prop
  have hdenpow : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ^ 2 ≠ 0 :=
    pow_ne_zero _ hden
  unfold oddStarBoundaryFactorSlope
  fun_prop (discharger := assumption)

theorem oddStarBoundaryLogSlope_joint_continuousAt
    (t θ : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane) :
    ContinuousAt (fun p : ℝ × ℝ =>
      oddStarBoundaryLogSlope
        (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1) (t, θ) := by
  have hfactor := oddStarBoundaryFactor_joint_continuousAt t θ hden
  have hslope := oddStarBoundaryFactorSlope_joint_continuousAt t θ ht hden
  have hLne := Complex.slitPlane_ne_zero hslit
  unfold oddStarBoundaryLogSlope
  fun_prop (discharger := assumption)

theorem oddStarMovingBoundaryPointSlope_joint_continuousAt
    (m : ℕ) (hm : 3 ≤ m) (t θ : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane) :
    ContinuousAt (fun p : ℝ × ℝ =>
      oddStarMovingBoundaryPointSlope m
        (oddStarBoundaryRadius m p.2) p.2 p.1) (t, θ) := by
  have hfactor := oddStarBoundaryFactor_joint_continuousAt t θ hden
  have hlog := hfactor.clog hslit
  have hlogslope := oddStarBoundaryLogSlope_joint_continuousAt
    t θ ht hden hslit
  have hr : ContinuousAt (oddStarBoundaryRadius m) θ :=
    (oddStarBoundaryRadius_continuous m hm).continuousAt
  have hrjoint : ContinuousAt
      (fun p : ℝ × ℝ => oddStarBoundaryRadius m p.2) (t, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.2) (t, θ) := continuousAt_snd
    exact hr.comp hp
  unfold oddStarMovingBoundaryPointSlope
  fun_prop

theorem oddStarTipRadiusSlope_joint_continuousAt
    (m : ℕ) (t θ : ℝ) (ht : |t| < 1) :
    ContinuousAt (fun p : ℝ × ℝ => oddStarTipRadiusSlope m p.1) (t, θ) := by
  have hbase : 0 < 1 - t ^ 2 := by
    have hlt := abs_lt.mp ht
    nlinarith
  have hden : 2 * Real.sqrt (1 - t ^ 2) ≠ 0 := by
    positivity
  have hbase4 : 4 * Real.sqrt (1 - t ^ 2) ≠ 0 := by
    positivity
  have hinner : ContinuousAt (fun p : ℝ × ℝ =>
      4 * Real.sqrt (1 - p.1 ^ 2)) (t, θ) := by
    fun_prop
  have hpow : ContinuousAt (fun p : ℝ × ℝ =>
      (4 * Real.sqrt (1 - p.1 ^ 2)) ^ ((m : ℝ)⁻¹ - 1)) (t, θ) := by
    exact ContinuousAt.comp
      (f := fun p : ℝ × ℝ => 4 * Real.sqrt (1 - p.1 ^ 2))
      (g := fun x : ℝ => x ^ ((m : ℝ)⁻¹ - 1))
      (x := (t, θ))
      (Real.continuousAt_rpow_const
        (4 * Real.sqrt (1 - t ^ 2)) ((m : ℝ)⁻¹ - 1) (Or.inl hbase4))
      hinner
  have hfrac : ContinuousAt (fun p : ℝ × ℝ =>
      (-2 * p.1) / (2 * Real.sqrt (1 - p.1 ^ 2))) (t, θ) := by
    fun_prop (discharger := assumption)
  change ContinuousAt (fun p : ℝ × ℝ =>
    ((m : ℝ)⁻¹) *
      (4 * Real.sqrt (1 - p.1 ^ 2)) ^ ((m : ℝ)⁻¹ - 1) *
        (4 * ((-2 * p.1) / (2 * Real.sqrt (1 - p.1 ^ 2))))) (t, θ)
  exact (continuousAt_const.mul hpow).mul (continuousAt_const.mul hfrac)

theorem oddStarMovingBoundaryPoint_joint_continuousAt_general
    (m : ℕ) (hm : 3 ≤ m) (t θ : ℝ)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane) :
    ContinuousAt
      (fun p : ℝ × ℝ => oddStarMovingBoundaryPoint m
        (oddStarBoundaryRadius m p.2) p.2 p.1) (t, θ) := by
  have hfactor := oddStarBoundaryFactor_joint_continuousAt t θ hden
  have hlog := hfactor.clog hslit
  have hr : ContinuousAt (oddStarBoundaryRadius m) θ :=
    (oddStarBoundaryRadius_continuous m hm).continuousAt
  have hrjoint : ContinuousAt
      (fun p : ℝ × ℝ => oddStarBoundaryRadius m p.2) (t, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.2) (t, θ) := continuousAt_snd
    exact hr.comp hp
  change ContinuousAt (fun p : ℝ × ℝ =>
    (oddStarBoundaryRadius m p.2 : ℂ) * Complex.exp
      (((m : ℂ)⁻¹) * Complex.log
        (oddStarBoundaryFactor (Complex.exp ((p.2 : ℂ) * Complex.I)) p.1)))
      (t, θ)
  fun_prop

theorem oddStarOppositeTipLogSlope_joint_continuousAt
    (m : ℕ) (hm : 3 ≤ m) (t θ : ℝ) (ht : |t| < 1)
    (hden : oddStarBoundaryDenominator
      (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0)
    (hslit : oddStarBoundaryFactor
      (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane)
    (hdist : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => oddStarOppositeTipLogSlope m p.2 p.1)
      (t, θ) := by
  have hZ := oddStarMovingBoundaryPoint_joint_continuousAt_general
    m hm t θ hden hslit
  have hZslope := oddStarMovingBoundaryPointSlope_joint_continuousAt
    m hm t θ ht hden hslit
  have hR : ContinuousAt (oddStarTipRadius m) t :=
    (oddStarTipRadius_differentiableAt m t ht).continuousAt
  have hRjoint : ContinuousAt
      (fun p : ℝ × ℝ => oddStarTipRadius m p.1) (t, θ) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => p.1) (t, θ) := continuousAt_fst
    have hR' : ContinuousAt (oddStarTipRadius m)
        ((fun p : ℝ × ℝ => p.1) (t, θ)) := by
      simpa using hR
    exact hR'.comp hp
  have hRslope := oddStarTipRadiusSlope_joint_continuousAt m t θ ht
  have hDne :
      ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hdist)
  change ContinuousAt (fun p : ℝ × ℝ =>
    ⟪oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m p.2) p.2 p.1 -
        (oddStarTipRadius m p.1 : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I),
      oddStarMovingBoundaryPointSlope m (oddStarBoundaryRadius m p.2) p.2 p.1 -
        (oddStarTipRadiusSlope m p.1 : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)⟫ /
      ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m p.2) p.2 p.1 -
        (oddStarTipRadius m p.1 : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ ^ 2)
      (t, θ)
  fun_prop (discharger := assumption)

theorem oddStarOppositeTipLogSlope_uniform_bound
    (m : ℕ) (hm : 3 ≤ m) :
    ∃ ε M : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc (-ε) ε,
        ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
          HasDerivAt (oddStarOppositeTipLogDistance m θ)
            (oddStarOppositeTipLogSlope m θ t) t ∧
          |oddStarOppositeTipLogSlope m θ t| ≤ M := by
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hU hV)
  let ε : ℝ := a / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let I : Set ℝ := Set.Icc (-ε) ε
  let K : Set ℝ := Set.Icc (0 : ℝ) (2 * Real.pi)
  let S : Set (ℝ × ℝ) := I ×ˢ K
  have hmem (t : ℝ) (ht : t ∈ I) : t ∈ U ∩ V := by
    have habs : |t| ≤ ε := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq] using
      (lt_of_le_of_lt habs (by dsimp [ε]; linarith : ε < a))
  have hRpos : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => |oddStarOppositeTipLogSlope m p.2 p.1|) S := by
    intro p hp
    rcases p with ⟨t, θ⟩
    obtain ⟨ht, hθ⟩ := hp
    have htv := hmem t ht
    have ht1 : |t| < 1 := by
      have h : t ∈ V := htv.2
      simpa [V, abs_lt] using h
    have hprops := hreg t htv.1 θ hθ
    have hdist : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0 := by
      intro heq
      rw [heq, norm_zero] at hprops
      linarith [hprops.1]
    have h := oddStarOppositeTipLogSlope_joint_continuousAt
      m hm t θ ht1 hprops.2.2 hprops.2.1 hdist
    exact h.abs.continuousWithinAt
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hbound : BddAbove
      ((fun p : ℝ × ℝ => |oddStarOppositeTipLogSlope m p.2 p.1|) '' S) :=
    (hcompact.image_of_continuousOn hcont).bddAbove
  obtain ⟨M, hM⟩ := hbound
  refine ⟨ε, M, hε, ?_⟩
  intro t ht θ hθ
  have htv := hmem t ht
  have ht1 : |t| < 1 := by
    have h : t ∈ V := htv.2
    simpa [V, abs_lt] using h
  have hprops := hreg t htv.1 θ hθ
  have hdist : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hprops
    linarith [hprops.1]
  constructor
  · exact oddStarOppositeTipLogDistance_hasDerivAt_general
      m θ t ht1 hprops.2.2 hprops.2.1 hdist
  · have hp : (t, θ) ∈ S := ⟨ht, hθ⟩
    have himg : |oddStarOppositeTipLogSlope m θ t| ∈
        ((fun p : ℝ × ℝ => |oddStarOppositeTipLogSlope m p.2 p.1|) '' S) :=
      ⟨(t, θ), hp, rfl⟩
    exact hM himg

end SpringerLean
