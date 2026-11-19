import SpringerLean.Round08General

open scoped Topology

namespace SpringerLean

/-- Actual omitted set of an exterior map, with no assumed boundary curve. -/
def exteriorOmitted (F : ℂ → ℂ) : Set ℂ := (F '' exteriorDisk)ᶜ

/-- Omitted set at source radius `1/s`, before scaling the image. -/
def exteriorOmittedAtScale (F : ℂ → ℂ) (s : ℝ) : Set ℂ :=
  (F '' exteriorAbove s⁻¹)ᶜ

theorem scale_mem_exteriorDisk_iff
    {s : ℝ} (hs : 0 < s) (z : ℂ) :
    (s : ℂ) * z ∈ exteriorDisk ↔ z ∈ exteriorAbove s⁻¹ := by
  change 1 < ‖(s : ℂ) * z‖ ↔ s⁻¹ < ‖z‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hsne : s ≠ 0 := hs.ne'
  have hinv : s * s⁻¹ = 1 := by field_simp
  constructor
  · intro h
    by_contra hnot
    have hle : ‖z‖ ≤ s⁻¹ := le_of_not_gt hnot
    have hmul := mul_le_mul_of_nonneg_left hle hs.le
    nlinarith
  · intro h
    have hmul := mul_lt_mul_of_pos_left h hs
    nlinarith

/-- The actual omitted set of `F_s` equals the scaled omitted set of the
unscaled map on the larger source exterior domain. -/
theorem rescaleExterior_omitted_eq_image
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s) :
    exteriorOmitted (rescaleExterior s F) =
      (fun w : ℂ => (s : ℂ) * w) '' exteriorOmittedAtScale F s := by
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  ext w
  constructor
  · intro hw
    let v : ℂ := w / (s : ℂ)
    have hvEq : (s : ℂ) * v = w := by
      dsimp [v]
      field_simp
    refine ⟨v, ?_, hvEq⟩
    intro hv
    obtain ⟨z, hz, hF⟩ := hv
    have hzS : (s : ℂ) * z ∈ exteriorDisk :=
      (scale_mem_exteriorDisk_iff hs z).mpr hz
    apply hw
    refine ⟨(s : ℂ) * z, hzS, ?_⟩
    change (s : ℂ) * F (((s : ℂ) * z) / (s : ℂ)) = w
    rw [mul_div_cancel_left₀ z hsne, hF]
    exact hvEq
  · rintro ⟨v, hv, rfl⟩
    intro hw
    obtain ⟨z, hz, hF⟩ := hw
    let y : ℂ := z / (s : ℂ)
    have hy : y ∈ exteriorAbove s⁻¹ := by
      have hzEq : (s : ℂ) * y = z := by
        dsimp [y]
        field_simp
      rw [← hzEq] at hz
      exact (scale_mem_exteriorDisk_iff hs y).mp hz
    apply hv
    refine ⟨y, hy, ?_⟩
    have h : (s : ℂ) * F y = (s : ℂ) * v := hF
    exact mul_left_cancel₀ hsne h

/-- The actual omitted set is bounded, using the verified inverse branch
near infinity. This supplies the finiteness needed for weighted area limits. -/
theorem exteriorOmitted_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ M : ℝ, 0 < M ∧ ∀ w ∈ exteriorOmitted F, ‖w‖ ≤ M := by
  obtain ⟨δ, hδ, hδprop⟩ :=
    Metric.mem_nhds_iff.mp (exterior_inverse_covers_near_infinity F hc)
  refine ⟨δ⁻¹ + 1, by positivity, ?_⟩
  intro w hw
  by_contra hbad
  have hlarge : δ⁻¹ + 1 < ‖w‖ := lt_of_not_ge hbad
  have hw0 : w ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hlarge
    have hδinv : 0 < δ⁻¹ := inv_pos.mpr hδ
    linarith
  let t : ℂ := w⁻¹
  have ht0 : t ≠ 0 := inv_ne_zero hw0
  have htNorm : ‖t‖ < δ := by
    change ‖w⁻¹‖ < δ
    rw [norm_inv]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hmul : 1 < δ * ‖w‖ := by
      calc
        (1 : ℝ) = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
        _ < δ * ‖w‖ := mul_lt_mul_of_pos_left
          (by linarith : δ⁻¹ < ‖w‖) hδ
    exact (inv_lt_iff_one_lt_mul₀ hwpos).mpr hmul
  have htmem : t ∈ Metric.ball (0 : ℂ) δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using htNorm
  have hwImage := hδprop htmem ht0
  change w⁻¹⁻¹ ∈ F '' exteriorDisk at hwImage
  rw [inv_inv] at hwImage
  exact hw hwImage

/-- The actual omitted set is Borel measurable by Lusin–Souslin applied
to the continuous injective exterior restriction. -/
theorem exteriorOmitted_measurableSet
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    MeasurableSet (exteriorOmitted F) := by
  have hcont : ContinuousOn F exteriorDisk := hc.1.continuousOn
  exact (exteriorDisk_isOpen.measurableSet.image_of_continuousOn_injOn
    hcont hc.2.1).compl

/-- Every polynomial weight has a finite integral over the actual omitted
set. The bound comes from the verified inverse branch. -/
theorem exteriorOmitted_weight_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun w : ℂ => ‖w‖ ^ m)
      (exteriorOmitted F) := by
  obtain ⟨M, hM0, hM⟩ := exteriorOmitted_bounded F hc
  have hsub : exteriorOmitted F ⊆ Metric.closedBall (0 : ℂ) M := by
    intro w hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using hM w hw
  have hcont : Continuous (fun w : ℂ => ‖w‖ ^ m) :=
    continuous_norm.pow m
  exact (hcont.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) M)).mono_set hsub

/-- As `s` increases, the unscaled omitted sets decrease. -/
theorem exteriorOmittedAtScale_antitone
    (F : ℂ → ℂ) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    exteriorOmittedAtScale F t ⊆ exteriorOmittedAtScale F s := by
  intro w hw
  intro hws
  obtain ⟨z, hz, hF⟩ := hws
  have hInv : t⁻¹ ≤ s⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hs hst
  exact hw ⟨z, lt_of_le_of_lt hInv hz, hF⟩

/-- The intersection of the unscaled omitted sets as `s↑1` is exactly the
actual omitted set. This is a pointwise set statement; weighted measure
continuity remains a later step. -/
theorem exteriorOmitted_iff_all_scales
    (F : ℂ → ℂ) (w : ℂ) :
    w ∈ exteriorOmitted F ↔
      ∀ s : ℝ, 0 < s → s < 1 → w ∈ exteriorOmittedAtScale F s := by
  constructor
  · intro hw s hs0 hs1
    intro hws
    obtain ⟨z, hz, hF⟩ := hws
    have hInv : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
    exact hw ⟨z, lt_trans hInv hz, hF⟩
  · intro hall
    intro hw
    obtain ⟨z, hz, hF⟩ := hw
    change 1 < ‖z‖ at hz
    let r : ℝ := (‖z‖ + 1) / 2
    have hr1 : 1 < r := by
      dsimp [r]
      linarith
    have hrz : r < ‖z‖ := by
      dsimp [r]
      linarith
    let s : ℝ := r⁻¹
    have hs0 : 0 < s := inv_pos.mpr (by linarith : 0 < r)
    have hs1 : s < 1 := inv_lt_one_of_one_lt₀ hr1
    have hKs := hall s hs0 hs1
    apply hKs
    refine ⟨z, ?_, hF⟩
    change s⁻¹ < ‖z‖
    simpa only [s, inv_inv] using hrz

/-- Every intermediate omitted set `K_s` is Borel measurable, with only
the original exterior class as hypothesis. -/
theorem exteriorOmittedAtScale_measurableSet
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    MeasurableSet (exteriorOmittedAtScale F s) := by
  have hInv : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hsub : exteriorAbove s⁻¹ ⊆ exteriorDisk := by
    intro z hz
    exact lt_trans hInv hz
  have hOpen : IsOpen (exteriorAbove s⁻¹) :=
    isOpen_lt continuous_const continuous_norm
  have hcont : ContinuousOn F (exteriorAbove s⁻¹) :=
    hc.1.continuousOn.mono hsub
  have hInj : Set.InjOn F (exteriorAbove s⁻¹) :=
    hc.2.1.mono hsub
  exact (hOpen.measurableSet.image_of_continuousOn_injOn
    hcont hInj).compl

/-- Each intermediate omitted set is bounded because its scaled image is
the omitted set of the actual regular dilate. -/
theorem exteriorOmittedAtScale_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ w ∈ exteriorOmittedAtScale F s, ‖w‖ ≤ M := by
  have hcS := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  obtain ⟨M, hM0, hM⟩ := exteriorOmitted_bounded
    (rescaleExterior s F) hcS
  refine ⟨M / s, div_pos hM0 hs0, ?_⟩
  intro w hw
  have hscaled : (s : ℂ) * w ∈ exteriorOmitted (rescaleExterior s F) := by
    rw [rescaleExterior_omitted_eq_image F hs0]
    exact ⟨w, hw, rfl⟩
  have hbound := hM ((s : ℂ) * w) hscaled
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at hbound
  exact (le_div_iff₀ hs0).mpr (by simpa only [mul_comm] using hbound)

theorem exteriorOmittedAtScale_weight_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun w : ℂ => ‖w‖ ^ m)
      (exteriorOmittedAtScale F s) := by
  obtain ⟨M, hM0, hM⟩ := exteriorOmittedAtScale_bounded F hc hs0 hs1
  have hsub : exteriorOmittedAtScale F s ⊆ Metric.closedBall (0 : ℂ) M := by
    intro w hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using hM w hw
  exact ((continuous_norm.pow m).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : ℂ) M)).mono_set hsub

end SpringerLean
