import SpringerLean.RegularFirst

open Filter
open scoped Topology

namespace SpringerLean

/-- The actual inverse branch near infinity bounds the original exterior
map on the fixed annulus next to the unit circle. -/
theorem exteriorMap_bounded_near_unitCircle
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ M : ℝ, 0 < M ∧
      ∀ z ∈ exteriorDisk, ‖z‖ ≤ 2 → ‖F z‖ ≤ M := by
  rcases exterior_actualInverse_local_branch F hc with
    ⟨V, hV0, hVa, hVder, hright, hbranch, hcomp⟩
  have hVsmall : ∀ᶠ t : ℂ in 𝓝 0, ‖V t‖ < 1 / 2 := by
    have hball : Metric.ball (V 0) (1 / 2 : ℝ) ∈ 𝓝 (V 0) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [hVa.continuousAt.tendsto.eventually hball] with t ht
    simpa only [hV0, Metric.mem_ball, dist_zero_right] using ht
  have hlocal : ∀ᶠ t : ℂ in 𝓝 0,
      t ≠ 0 → V t ≠ 0 ∧ (V t)⁻¹ ∈ exteriorDisk ∧
        F (V t)⁻¹ = t⁻¹ ∧ ‖V t‖ < 1 / 2 := by
    filter_upwards [hbranch, hVsmall] with t ht hs ht0
    obtain ⟨hVne, hVext, hF, hInv⟩ := ht ht0
    exact ⟨hVne, hVext, hF, hs⟩
  obtain ⟨ε, hε, hεprop⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro z hz hz2
  by_contra hbad
  have hlarge : ε⁻¹ < ‖F z‖ := lt_of_not_ge hbad
  have hF0 : F z ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hlarge
    linarith [inv_pos.mpr hε]
  let t : ℂ := (F z)⁻¹
  have ht0 : t ≠ 0 := inv_ne_zero hF0
  have htNorm : ‖t‖ < ε := by
    change ‖(F z)⁻¹‖ < ε
    rw [norm_inv]
    have hFpos : 0 < ‖F z‖ := norm_pos_iff.mpr hF0
    have hmul : 1 < ε * ‖F z‖ := by
      calc
        (1 : ℝ) = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
        _ < ε * ‖F z‖ := mul_lt_mul_of_pos_left hlarge hε
    exact (inv_lt_iff_one_lt_mul₀ hFpos).mpr hmul
  have htmem : t ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right] using htNorm
  obtain ⟨hVne, hVext, hF, hVnorm⟩ := hεprop htmem ht0
  have hsame : z = (V t)⁻¹ := by
    apply hc.2.1 hz hVext
    simpa only [t, inv_inv] using hF.symm
  have hVpos : 0 < ‖V t‖ := norm_pos_iff.mpr hVne
  have hVlarge : 2 < ‖(V t)⁻¹‖ := by
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt hVpos hVnorm
    norm_num at h
    simpa only [one_div] using h
  rw [hsame] at hz2
  linarith

/-- The normalized forward correction is uniformly bounded on the open
unit disk; this uses univalence through the actual inverse branch. -/
theorem exteriorForwardGerm_bounded_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℂ, ‖u‖ < 1 → ‖exteriorForwardGerm F u‖ ≤ C := by
  obtain ⟨M, hMpos, hM⟩ := exteriorMap_bounded_near_unitCircle F hc
  have hcont : ContinuousOn (exteriorForwardGerm F)
      (Metric.closedBall (0 : ℂ) (1 / 2 : ℝ)) :=
    (exteriorForwardGerm_analyticOnNhd_unitBall F hc).continuousOn.mono
      (Metric.closedBall_subset_ball (by norm_num))
  obtain ⟨B, hB⟩ :=
    (((isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ)).image_of_continuousOn
      hcont).isBounded.exists_norm_le)
  have hinner : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → ‖exteriorForwardGerm F u‖ ≤ B := by
    intro u hu
    exact hB _ (Set.mem_image_of_mem _
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu))
  refine ⟨max B (M + 2), by linarith [le_max_right B (M + 2)], ?_⟩
  intro u hu
  by_cases hhalf : ‖u‖ ≤ 1 / 2
  · exact (hinner u hhalf).trans (le_max_left B (M + 2))
  · have hupos : 0 < ‖u‖ := by linarith
    have hu0 : u ≠ 0 := norm_pos_iff.mp hupos
    have hzext : u⁻¹ ∈ exteriorDisk := by
      change 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hupos).mpr hu
    have hz2 : ‖u⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hlow : 1 / 2 ≤ ‖u‖ := le_of_not_ge hhalf
      have hq : 1 / ‖u‖ ≤ 2 :=
        (div_le_iff₀ hupos).mpr (by nlinarith)
      simpa only [one_div] using hq
    have hfu := exteriorForwardGerm_punctured F hu0
    rw [hfu]
    calc
      ‖F u⁻¹ - u⁻¹‖ ≤ ‖F u⁻¹‖ + ‖u⁻¹‖ := norm_sub_le _ _
      _ ≤ M + 2 := add_le_add (hM u⁻¹ hzext hz2) hz2
      _ ≤ max B (M + 2) := le_max_right _ _

end SpringerLean
