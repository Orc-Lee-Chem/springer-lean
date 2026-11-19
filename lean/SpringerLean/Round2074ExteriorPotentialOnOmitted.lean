import SpringerLean.Round2072ExteriorCircleSmoothing
import SpringerLean.Round2073LogPotentialDiagonal

open Metric Set Real Filter Bornology MeasureTheory
open scoped Topology

namespace SpringerLean

/-- Every omitted point has a neighborhood within each enlarged omitted
set. At infinity the exterior map differs from the identity by a
function tending to zero. On a bounded closed source annulus the image
is compact and does not contain the omitted point. -/
theorem exteriorOmitted_mem_interior_atScale
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (hx : x ∈ exteriorOmitted F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    x ∈ interior (exteriorOmittedAtScale F s) := by
  have hR : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
  have hg : Tendsto (fun w : ℂ => exteriorForwardGerm F w⁻¹) (cobounded ℂ)
      (𝓝 (0 : ℂ)) := by
    simpa only [Function.comp_def, exteriorForwardGerm_zero] using
      hF.2.2.continuousAt.tendsto.comp tendsto_inv₀_cobounded
  have hnear : ∀ᶠ w : ℂ in cobounded ℂ, ‖F w - w‖ < 1 := by
    filter_upwards [hg.norm.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1)),
      eventually_cobounded_le_norm (E := ℂ) 1] with w hw hw1
    have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (by linarith : ‖w‖ ≠ 0)
    simpa only [exteriorForwardGerm_punctured F (inv_ne_zero hw0), inv_inv] using hw
  obtain ⟨M, -, hM⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.mp hnear
  let L := max M (‖x‖ + 2)
  let A : Set ℂ := closedBall 0 L ∩ (ball 0 s⁻¹)ᶜ
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_right isOpen_ball.isClosed_compl
  have hsub : A ⊆ exteriorDisk := by
    intro w hw
    change 1 < ‖w‖
    exact hR.trans_le (by simpa [mem_ball, dist_zero_right] using hw.2)
  have hclosed : IsClosed (F '' A) :=
    (hA.image_of_continuousOn (hF.1.continuousOn.mono hsub)).isClosed
  have hxm : x ∈ (F '' A)ᶜ := fun ⟨w, hw, he⟩ => hx ⟨w, hsub hw, he⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hxm)
  rw [mem_interior_iff_mem_nhds]
  apply mem_of_superset (ball_mem_nhds x (lt_min hδ zero_lt_one))
  intro y hy
  have hd : ‖y - x‖ < min δ 1 := by simpa [mem_ball, dist_eq_norm] using hy
  have hyF := hball (show y ∈ ball x δ from
    by simpa [mem_ball, dist_eq_norm] using hd.trans_le (min_le_left _ _))
  change y ∉ F '' exteriorAbove s⁻¹
  rintro ⟨w, hw, rfl⟩
  have hw' : s⁻¹ < ‖w‖ := hw
  apply hyF
  refine ⟨w, ⟨?_, ?_⟩, rfl⟩
  · by_contra! hout
    have hwL : L < ‖w‖ := by simpa [mem_closedBall, dist_zero_right] using hout
    have hsmall := hM (show w ∈ (closedBall (0 : ℂ) M)ᶜ from by
      simpa [mem_closedBall, dist_zero_right] using (le_max_left _ _).trans_lt hwL)
    have hnormF : ‖F w‖ < ‖x‖ + 1 := by
      calc
        ‖F w‖ = ‖F w - x + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖F w - x‖ + ‖x‖ := norm_add_le _ _
        _ < ‖x‖ + 1 := by linarith [hd.trans_le (min_le_right δ (1 : ℝ))]
    have hwle : ‖w‖ ≤ ‖F w - w‖ + ‖F w‖ := by
      calc
        ‖w‖ = ‖(w - F w) + F w‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - F w‖ + ‖F w‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev w]
    linarith [(le_max_right M (‖x‖ + 2)).trans_lt hwL]
  · simpa [mem_ball, dist_zero_right] using hw'.le

/-- Near an omitted point, circle averaging gives an arbitrarily small
upper bound for the truncated potential of the actual radial law. -/
theorem actualExteriorBoundaryProbability_small_clippedLog_le
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (hx : x ∈ exteriorOmitted F)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 5)
    (hcircle : sphere x ε ⊆ exteriorOmittedAtScale F s) :
    (∫ z, clippedLogDistance x ε 5 hε hε5 z ∂actualExteriorBoundaryProbability F)
      ≤ -Real.log s := by
  let φ := clippedLogDistance x ε 5 hε hε5
  apply le_of_tendsto (smoothExteriorBoundaryProbability_boundedTest_tendsto F hF φ)
  filter_upwards [Ioo_mem_nhdsLT hs1] with r hr
  have hr0 : 0 < r := hs0.trans hr.1
  have hR : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr.2
  have hsub : sphere (0 : ℂ) |r⁻¹| ⊆ exteriorDisk := by
    intro z hz
    change 1 < ‖z‖
    have hn : ‖z‖ = r⁻¹ := by
      simpa [mem_sphere, dist_zero_right, abs_of_pos (inv_pos.mpr hr0)] using hz
    rwa [hn]
  have hFc := hF.1.continuousOn.mono hsub
  have hφint : CircleIntegrable (fun z => φ (F z)) 0 r⁻¹ :=
    (φ.continuous.comp_continuousOn hFc).circleIntegrable'
  have hlogc : ContinuousOn (fun z => Real.log (max ε ‖F z - x‖))
      (sphere (0 : ℂ) |r⁻¹|) := by
    apply (continuousOn_const.sup (hFc.sub continuousOn_const).norm).log
    exact fun z _ => (hε.trans_le (le_max_left _ _)).ne'
  rw [smoothExteriorBoundaryProbability_integral_eq_circleAverage F hF r hr0 hr.2
    φ φ.continuous.measurable]
  have hle := circleAverage_mono hφint hlogc.circleIntegrable' (fun z _ =>
    Real.log_le_log
      (lt_min (by norm_num : (0 : ℝ) < 5) (hε.trans_le (le_max_left _ _)))
      (min_le_right _ _))
  refine hle.trans ?_
  rw [← exterior_circleAverage_log_potential_smoothing F hF x r⁻¹ ε hR hε]
  have hpot (y : ℂ) (hy : y ∈ sphere x |ε|) :
      circleAverage (fun z => Real.log ‖F z - y‖) 0 r⁻¹ ≤ -Real.log s := by
    have hyK := hcircle (by simpa [abs_of_pos hε] using hy)
    by_cases h : y ∈ F '' exteriorDisk
    · obtain ⟨w, hw, rfl⟩ := h
      have hsw : ‖w‖ ≤ s⁻¹ := by
        by_contra! hlt
        exact hyK ⟨w, hlt, rfl⟩
      rw [exterior_circle_log_potential_at_image F hF w hw r hr0 hr.2, ← Real.log_inv]
      exact Real.log_le_log ((inv_pos.mpr hr0).trans_le (le_max_left _ _))
        (max_le (inv_anti₀ hs0 hr.1.le) hsw)
    · rw [exterior_circle_log_potential_of_omitted F hF y h r hr0 hr.2]
      exact neg_le_neg (Real.log_le_log hs0 hr.1.le)
  by_cases hi : CircleIntegrable (fun y => circleAverage
      (fun z => Real.log ‖F z - y‖) 0 r⁻¹) x ε
  · exact circleAverage_mono_on_of_le_circle hi hpot
  · rw [circleAverage_def, intervalIntegral.integral_undef hi, smul_zero]
    exact neg_nonneg.mpr (Real.log_nonpos hs0.le hs1.le)

/-- The actual radial probability has constant logarithmic potential
zero on the entire omitted set. The integral uses an integrable kernel
off the diagonal and the law has no atom at the evaluation point. -/
theorem actualExteriorBoundaryProbability_log_potential_on_omitted
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ)
    (hx : x ∈ exteriorOmitted F) :
    (∫ z, Real.log ‖z - x‖ ∂actualExteriorBoundaryProbability F) = 0 := by
  obtain ⟨hne, hi, hnonneg⟩ :=
    actualExteriorBoundaryProbability_log_potential_integrable_on_omitted F hF x hx
  apply le_antisymm _ hnonneg
  by_contra! hp
  let b : ℝ := (∫ z, Real.log ‖z - x‖ ∂actualExteriorBoundaryProbability F) / 2
  have hb : 0 < b := half_pos hp
  let s : ℝ := Real.exp (-b)
  have hs0 : 0 < s := Real.exp_pos _
  have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp
    (exteriorOmitted_mem_interior_atScale F hF x hx s hs0 hs1))
  let ε := min (δ / 2) 1
  have hε : 0 < ε := lt_min (half_pos hδ) zero_lt_one
  have hε5 : ε ≤ 5 := (min_le_right _ _).trans (by norm_num)
  have hc : sphere x ε ⊆ exteriorOmittedAtScale F s := by
    intro y hy
    apply hball
    rw [mem_ball, (mem_sphere.mp hy)]
    exact (min_le_left _ _).trans_lt (by linarith)
  let μ := actualExteriorBoundaryProbability F
  let φ := clippedLogDistance x ε 5 hε hε5
  have hμ : exteriorOmitted F ∈ ae μ :=
    actualExteriorBoundaryProbability_ae_mem_omitted F hF (exteriorOmitted_isCompact F hF).isClosed
  have hprob : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hl : (∫ z, Real.log ‖z - x‖ ∂μ) ≤ ∫ z, φ z ∂μ := by
    apply integral_mono_ae hi (BoundedContinuousFunction.integrable μ φ)
    filter_upwards [hne, hμ] with z hz hzK
    have hdist : ‖z - x‖ ≤ 5 := (norm_sub_le _ _).trans (by
      linarith [exteriorOmitted_norm_le_two F hF hzK, exteriorOmitted_norm_le_two F hF hx])
    exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hz))
      (le_min hdist (le_max_right _ _))
  have hu := actualExteriorBoundaryProbability_small_clippedLog_le
    F hF x hx s hs0 hs1 ε hε hε5 hc
  have hle := hl.trans hu
  dsimp [μ, s] at hle
  rw [Real.log_exp, neg_neg] at hle
  dsimp [b] at hle
  linarith

end SpringerLean
