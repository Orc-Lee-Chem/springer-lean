import SpringerLean.Round2013OddStarStrictLogWitness

namespace SpringerLean
open scoped Topology
open MeasureTheory

theorem continuumFarthestDistance_ge_distance
    (K : Set ℂ) (hK : IsCompact K)
    (z w : ℂ) (hw : w ∈ K) :
    ‖z - w‖ ≤ continuumFarthestDistance K z := by
  let f : ℂ → ℝ := fun w => ‖z - w‖
  have hf : Continuous f := by fun_prop
  have hcomp : IsCompact (f '' K) := hK.image hf
  have hb : BddAbove (f '' K) := hcomp.bddAbove
  exact le_csSup hb ⟨w, hw, rfl⟩

theorem continuumFarthestDistance_eq_distance_at_max
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (z : ℂ) :
    ∃ w ∈ K, continuumFarthestDistance K z = ‖z - w‖ := by
  obtain ⟨w, hw, hmax⟩ := continuumFarthestDistance_attained K hK hne z
  refine ⟨w, hw, le_antisymm ?_ (continuumFarthestDistance_ge_distance K hK z w hw)⟩
  apply csSup_le
  · exact ⟨‖z - w‖, ⟨w, hw, rfl⟩⟩
  rintro y ⟨v, hv, rfl⟩
  exact hmax v hv

theorem continuumFarthestDistance_lipschitz
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    LipschitzWith 1 (continuumFarthestDistance K) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  obtain ⟨w, hw, hd⟩ :=
    continuumFarthestDistance_eq_distance_at_max K hK hne z
  obtain ⟨w', hw', hd'⟩ :=
    continuumFarthestDistance_eq_distance_at_max K hK hne z'
  have hle : continuumFarthestDistance K z ≤
      continuumFarthestDistance K z' + ‖z - z'‖ := by
    rw [hd]
    have htri := dist_triangle z z' w
    have hbase := continuumFarthestDistance_ge_distance K hK z' w hw
    simp only [dist_eq_norm] at htri
    linarith
  have hle' : continuumFarthestDistance K z' ≤
      continuumFarthestDistance K z + ‖z - z'‖ := by
    rw [hd']
    have htri := dist_triangle z' z w'
    have hbase := continuumFarthestDistance_ge_distance K hK z w' hw'
    simp only [dist_eq_norm, norm_sub_rev z' z] at htri
    linarith
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem continuumFarthestDistance_continuous
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous (continuumFarthestDistance K) :=
  (continuumFarthestDistance_lipschitz K hK hne).continuous

theorem oddStarMovingBoundaryPoint_continuousOn_angle
    (m : ℕ) (hm : 3 ≤ m) (t : ℝ)
    (hreg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      oddStarBoundaryDenominator
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0 ∧
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane) :
    ContinuousOn
      (fun θ => oddStarMovingBoundaryPoint m
        (oddStarBoundaryRadius m θ) θ t)
      (Set.Icc 0 (2 * Real.pi)) := by
  intro θ hθ
  obtain ⟨hden, hslit⟩ := hreg θ hθ
  have h := oddStarMovingBoundaryPoint_joint_continuousAt_general
    m hm t θ hden hslit
  have hp : ContinuousAt (fun x : ℝ => (t, x)) θ := by fun_prop
  exact (h.comp hp).continuousWithinAt

theorem oddStarFarthestLog_continuousOn_angle
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (t : ℝ) (ht : |t| < 1)
    (hreg : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      oddStarBoundaryDenominator
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0 ∧
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane ∧
      0 < ‖oddStarMovingBoundaryPoint m
        (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖) :
    ContinuousOn
      (fun θ => Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t)
        (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t)))
      (Set.Icc 0 (2 * Real.pi)) := by
  let K := oddStarPerturbationOmitted m t
  have hK : IsCompact K := oddStarPerturbation_omitted_isCompact m (by omega) t ht
  have hne : K.Nonempty := ⟨0, (oddStarPerturbation_omitted_tips m (by omega) t ht).1⟩
  have hZ := oddStarMovingBoundaryPoint_continuousOn_angle m hm t
    (fun θ hθ => ⟨(hreg θ hθ).1, (hreg θ hθ).2.1⟩)
  have hdcont : ContinuousOn
      (fun θ => continuumFarthestDistance K
        (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t))
      (Set.Icc 0 (2 * Real.pi)) :=
    (continuumFarthestDistance_continuous K hK hne).comp_continuousOn hZ
  have htip := oddStarOppositeTip_mem_omitted m hm hodd t ht
  have hdpos (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
      0 < continuumFarthestDistance K
        (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t) := by
    exact (hreg θ hθ).2.2.trans_le
      (continuumFarthestDistance_ge_distance K hK _ _ htip)
  exact hdcont.log (fun θ hθ => ne_of_gt (hdpos θ hθ))

theorem oddStarOppositeTipLogDistance_le_farthestLog
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (t θ : ℝ) (ht : |t| < 1)
    (hdist : 0 < ‖oddStarMovingBoundaryPoint m
        (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖) :
    oddStarOppositeTipLogDistance m θ t ≤
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t)
        (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t)) := by
  have hK := oddStarPerturbation_omitted_isCompact m (by omega) t ht
  have htip := oddStarOppositeTip_mem_omitted m hm hodd t ht
  have hle := continuumFarthestDistance_ge_distance
    (oddStarPerturbationOmitted m t) hK
    (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t)
    ((oddStarTipRadius m t : ℂ) *
      Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)) htip
  exact Real.log_le_log hdist hle

theorem oddStarOppositeTipLogDistance_uniform_le_farthestLog
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U, ∀ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        oddStarOppositeTipLogDistance m θ t ≤
          Real.log (continuumFarthestDistance
            (oddStarPerturbationOmitted m t)
            (oddStarMovingBoundaryPoint m
              (oddStarBoundaryRadius m θ) θ t)) := by
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  intro t ht θ hθ
  have ht1 : |t| < 1 := by
    simpa [V, abs_lt] using ht.2
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hdist : 0 < ‖oddStarMovingBoundaryPoint m
      (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ := by
    have h := (hreg t ht.1 θ hθ).1
    linarith
  exact oddStarOppositeTipLogDistance_le_farthestLog
    m hm hodd t θ ht1 hdist

theorem oddStarOppositeTipLogDistance_integral_le_farthestLog
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ U : Set ℝ, U ∈ 𝓝 (0 : ℝ) ∧
      ∀ t ∈ U,
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          oddStarOppositeTipLogDistance m θ t) ≤
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          Real.log (continuumFarthestDistance
            (oddStarPerturbationOmitted m t)
            (oddStarMovingBoundaryPoint m
              (oddStarBoundaryRadius m θ) θ t))) := by
  obtain ⟨U, hU, hreg⟩ := oddStarVariation_uniform_regular_domain m hm
  let V : Set ℝ := Set.Ioo (-1 : ℝ) 1
  have hV : V ∈ 𝓝 (0 : ℝ) := by
    apply IsOpen.mem_nhds isOpen_Ioo
    norm_num [V]
  refine ⟨U ∩ V, Filter.inter_mem hU hV, ?_⟩
  intro t ht
  have ht1 : |t| < 1 := by simpa [V, abs_lt] using ht.2
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hreg' (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
      oddStarBoundaryDenominator
        (Complex.exp ((θ : ℂ) * Complex.I)) t ≠ 0 ∧
      oddStarBoundaryFactor
        (Complex.exp ((θ : ℂ) * Complex.I)) t ∈ Complex.slitPlane ∧
      0 < ‖oddStarMovingBoundaryPoint m
        (oddStarBoundaryRadius m θ) θ t -
        (oddStarTipRadius m t : ℂ) *
          Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ := by
    have hp := hreg t ht.1 θ hθ
    exact ⟨hp.2.2, hp.2.1, by linarith [hp.1]⟩
  have hFcont := oddStarOppositeTipLogDistance_continuousOn_angle
    m hm t ht1 (fun θ hθ =>
      ⟨(hreg' θ hθ).1, (hreg' θ hθ).2.1,
        norm_pos_iff.mp (hreg' θ hθ).2.2⟩)
  have hGcont := oddStarFarthestLog_continuousOn_angle
    m hm hodd t ht1 hreg'
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hFint : IntervalIntegrable
      (fun θ => oddStarOppositeTipLogDistance m θ t)
      volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc hpi hFcont
  have hGint : IntervalIntegrable
      (fun θ => Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t)
        (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t)))
      volume 0 (2 * Real.pi) :=
    ContinuousOn.intervalIntegrable_of_Icc hpi hGcont
  exact intervalIntegral.integral_mono_on hpi hFint hGint
    (fun θ hθ => oddStarOppositeTipLogDistance_le_farthestLog
      m hm hodd t θ ht1 (hreg' θ hθ).2.2)

end SpringerLean
