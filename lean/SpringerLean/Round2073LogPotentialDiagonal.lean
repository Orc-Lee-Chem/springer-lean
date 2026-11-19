import SpringerLean.Round2071TruncatedExteriorPotential

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

private theorem logCutoffRadius_pos (n : ℕ) : 0 < Real.exp (-(n : ℝ)) :=
  Real.exp_pos _

private theorem logCutoffRadius_le_five (n : ℕ) : Real.exp (-(n : ℝ)) ≤ 5 := by
  calc
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
    _ ≤ 5 := by norm_num

private noncomputable def logDistancePenaltyAt (x : ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  Real.log 5 - clippedLogDistance x (Real.exp (-(n : ℝ))) 5
    (logCutoffRadius_pos n) (logCutoffRadius_le_five n) z

private theorem logDistancePenaltyAt_continuous (x : ℂ) (n : ℕ) :
    Continuous (logDistancePenaltyAt x n) :=
  continuous_const.sub (clippedLogDistance _ _ _ _ _).continuous

private theorem logDistancePenaltyAt_nonneg (x z : ℂ) (n : ℕ) :
    0 ≤ logDistancePenaltyAt x n z := by
  unfold logDistancePenaltyAt
  rw [clippedLogDistance_apply, sub_nonneg]
  exact Real.log_le_log
    (lt_min (by norm_num) ((logCutoffRadius_pos n).trans_le (le_max_left _ _)))
    (min_le_left _ _)

private theorem logDistancePenaltyAt_mono (x : ℂ) :
    Monotone (logDistancePenaltyAt x) := by
  intro n m hnm z
  have hexp : Real.exp (-(m : ℝ)) ≤ Real.exp (-(n : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg (by exact_mod_cast hnm))
  unfold logDistancePenaltyAt
  simp only [clippedLogDistance_apply]
  apply sub_le_sub_left
  apply Real.log_le_log
  · exact lt_min (by norm_num)
      ((logCutoffRadius_pos m).trans_le (le_max_left _ _))
  · exact min_le_min le_rfl (max_le_max_right _ hexp)

private noncomputable def logDistancePenalty (x z : ℂ) : ENNReal :=
  ⨆ n : ℕ, ENNReal.ofReal (logDistancePenaltyAt x n z)

private theorem logDistancePenalty_measurable (x : ℂ) :
    Measurable (logDistancePenalty x) :=
  Measurable.iSup (fun n => (logDistancePenaltyAt_continuous x n).measurable.ennreal_ofReal)

private theorem logDistancePenalty_at_pole (x : ℂ) :
    logDistancePenalty x x = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro b
  obtain ⟨n, hn⟩ := exists_nat_gt (b : ℝ)
  apply le_trans _ (le_iSup (fun n => ENNReal.ofReal (logDistancePenaltyAt x n x)) n)
  rw [logDistancePenaltyAt, clippedLogDistance_apply, sub_self, norm_zero,
    max_eq_left (logCutoffRadius_pos n).le, min_eq_right (logCutoffRadius_le_five n),
    Real.log_exp, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 5)])

private theorem logDistancePenalty_away (x z : ℂ) (h : z ≠ x) (h5 : ‖z - x‖ ≤ 5) :
    logDistancePenalty x z = ENNReal.ofReal (Real.log 5 - Real.log ‖z - x‖) := by
  have hpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log ‖z - x‖)
  have hcut : Real.exp (-(N : ℝ)) ≤ ‖z - x‖ := by
    calc
      _ ≤ Real.exp (Real.log ‖z - x‖) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_log hpos
  apply le_antisymm
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    unfold logDistancePenaltyAt
    rw [clippedLogDistance_apply]
    exact sub_le_sub_left (Real.log_le_log hpos (le_min h5 (le_max_right _ _))) _
  · apply le_iSup_of_le N
    rw [logDistancePenaltyAt, clippedLogDistance_apply, max_eq_right hcut, min_eq_right h5]

/-- The actual radial law has no atom at an omitted point. Its logarithmic
potential there is integrable and nonnegative. In the proof the extended
kernel is infinite at its pole and is built as a monotone limit of
continuous finite cutoffs. -/
theorem actualExteriorBoundaryProbability_log_potential_integrable_on_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ) (hx : x ∈ exteriorOmitted F) :
    (∀ᵐ z ∂actualExteriorBoundaryProbability F, z ≠ x) ∧
      Integrable (fun z => Real.log ‖z - x‖) (actualExteriorBoundaryProbability F) ∧
      0 ≤ ∫ z, Real.log ‖z - x‖ ∂actualExteriorBoundaryProbability F := by
  let μ := actualExteriorBoundaryProbability F
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hμ : exteriorOmitted F ∈ ae μ :=
    actualExteriorBoundaryProbability_ae_mem_omitted F hF (exteriorOmitted_isCompact F hF).isClosed
  have h5 : ∀ᵐ z ∂μ, ‖z - x‖ ≤ 5 := by
    filter_upwards [hμ] with z hz
    exact (norm_sub_le _ _).trans (by
      linarith [exteriorOmitted_norm_le_two F hF hz, exteriorOmitted_norm_le_two F hF hx])
  have hb n : (∫⁻ z, ENNReal.ofReal (logDistancePenaltyAt x n z) ∂μ) ≤
      ENNReal.ofReal (Real.log 5) := by
    have hbounded := BoundedContinuousFunction.integrable μ
      (clippedLogDistance x _ _ (logCutoffRadius_pos n) (logCutoffRadius_le_five n))
    have hi : Integrable (logDistancePenaltyAt x n) μ := (integrable_const _).sub hbounded
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (fun z => logDistancePenaltyAt_nonneg x z n))]
    apply ENNReal.ofReal_le_ofReal
    simp only [logDistancePenaltyAt]
    rw [integral_sub (integrable_const _) hbounded]
    simpa only [integral_const, probReal_univ, one_smul, sub_le_self_iff] using
      actualExteriorBoundaryProbability_clippedLog_nonneg F hF x hx _
        (logCutoffRadius_pos n) (logCutoffRadius_le_five n)
  have hfin : (∫⁻ z, logDistancePenalty x z ∂μ) ≤ ENNReal.ofReal (Real.log 5) := by
    unfold logDistancePenalty
    rw [lintegral_iSup
      (fun n => (logDistancePenaltyAt_continuous x n).measurable.ennreal_ofReal)
      (fun n m hnm z => ENNReal.ofReal_le_ofReal (logDistancePenaltyAt_mono x hnm z))]
    exact iSup_le hb
  have hne : ∀ᵐ z ∂μ, z ≠ x := by
    filter_upwards [ae_lt_top (logDistancePenalty_measurable x)
      (hfin.trans_lt ENNReal.ofReal_lt_top).ne] with z hz
    rintro rfl
    exact hz.ne (logDistancePenalty_at_pole _)
  have hpen : (fun z => logDistancePenalty x z) =ᵐ[μ]
      fun z => ENNReal.ofReal (Real.log 5 - Real.log ‖z - x‖) := by
    filter_upwards [hne, h5] with z hz hz5
    exact logDistancePenalty_away x z hz hz5
  let g : ℂ → ℝ := fun z => Real.log 5 - Real.log ‖z - x‖
  have hg0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [hne, h5] with z hz hz5
    exact sub_nonneg.mpr (Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hz)) hz5)
  have hg : Integrable g μ := by
    refine ⟨(by fun_prop : Measurable g).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hg0, ← lintegral_congr_ae hpen]
    exact hfin.trans_lt ENNReal.ofReal_lt_top
  have hi : Integrable (fun z => Real.log ‖z - x‖) μ := by
    convert (integrable_const (Real.log 5)).sub hg using 1
    funext z
    dsimp [g]
    ring
  refine ⟨hne, hi, ?_⟩
  rw [lintegral_congr_ae hpen, ← ofReal_integral_eq_lintegral_ofReal hg hg0] at hfin
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hg0),
    ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))] at hb'
  dsimp only [g] at hb'
  rw [integral_sub (integrable_const _) hi, integral_const, probReal_univ, one_smul] at hb'
  linarith

end SpringerLean
