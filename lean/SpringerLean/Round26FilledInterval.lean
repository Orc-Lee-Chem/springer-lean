import SpringerLean.Round26NoInterval

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean

/-- If an open interval is occupied modulo null sets, one interval
contribution to the translation difference equals exactly the translation
length. -/
theorem realSet_shift_sdiff_lower_of_ae_filled_interval
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (c u : ℝ) (hcu : c < u) (hfull : volume (Ioo c u \ E) = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, 0 < d → d < δ →
      d ≤ volume.real (E \ verticalShiftPlus E d) := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hEb
  let M₀ : ℝ := max M 0
  let a : ℝ := min (-M₀ - 1) (c - 1)
  let b : ℝ := (c + u) / 2
  let δ : ℝ := b - c
  have hcb : c < b := by dsimp [b]; linarith
  have hbu : b < u := by dsimp [b]; linarith
  have hab : a < b := by
    have ha : a ≤ c - 1 := min_le_right _ _
    linarith
  have hδ : 0 < δ := sub_pos.mpr hcb
  refine ⟨δ, hδ, ?_⟩
  intro d hd0 hdδ
  have hbdc : c < b - d := by dsimp [δ] at hdδ; linarith
  have hI : Ioc (b - d) b ⊆ Ioo c u := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnull : volume (Ioc (b - d) b \ E) = 0 := by
    apply measure_mono_null (t := Ioo c u \ E) ?_ hfull
    intro t ht
    exact ⟨hI ht.1, ht.2⟩
  have hinter : volume (Ioc (b - d) b ∩ E) = volume (Ioc (b - d) b) := by
    have hsplit := measure_inter_add_sdiff (μ := volume) (Ioc (b - d) b) hE
    rw [hnull, add_zero] at hsplit
    exact hsplit
  have hfirst : (∫ t in (b - d)..b, realSetIndicator E t) = d := by
    rw [realSetIndicator_interval_integral_eq_measureReal E hE _ _ (by linarith),
      Measure.real_def, hinter, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ b - (b - d))]
    ring
  have hleft : Ioc (a - d) a ∩ E = ∅ := by
    ext t
    constructor
    · intro ht
      have htbound : |t| ≤ M₀ :=
        (show |t| ≤ M from by simpa [Real.norm_eq_abs] using hM t ht.2).trans
          (le_max_left _ _)
      have htlow := (abs_le.mp htbound).1
      have hta : t ≤ a := ht.1.2
      have ha : a ≤ -M₀ - 1 := min_le_left _ _
      linarith
    · simp
  have hsecond : (∫ t in (a - d)..a, realSetIndicator E t) = 0 := by
    rw [realSetIndicator_interval_integral_eq_measureReal E hE _ _ (by linarith),
      hleft]
    simp
  have hJ :
      (∫ t in a..b, realSetIndicator E t - realSetIndicator E (t - d)) = d := by
    rw [realSet_interval_shift_integral_eq E hE hEb a b d,
      realSetPrimitive_sub_eq_interval E hE hEb (b - d) b,
      realSetPrimitive_sub_eq_interval E hE hEb (a - d) a,
      hfirst, hsecond]
    ring
  have hbound := realSet_interval_shift_le_sdiff E hE hEb a b d hab.le
  rw [hJ] at hbound
  exact hbound

end SpringerLean
