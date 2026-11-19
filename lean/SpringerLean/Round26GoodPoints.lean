import SpringerLean.Round26TwoBoundaries

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean

/-- Any positive-measure real set contains two distinct points satisfying
an almost-everywhere property. The singleton removal uses atomlessness. -/
theorem positive_measure_exists_two_good_points
    (E : Set ℝ) (hEpos : volume E ≠ 0)
    (p : ℝ → Prop) (hp : ∀ᵐ x : ℝ, p x) :
    ∃ b₁ b₂ : ℝ, b₁ ∈ E ∧ b₂ ∈ E ∧ b₁ < b₂ ∧ p b₁ ∧ p b₂ := by
  obtain ⟨x, hxE, hxp⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hEpos (ae_restrict_of_ae hp)
  have hremove : volume (E \ {x}) = volume E := by
    apply measure_sdiff_null'
    exact measure_mono_null inter_subset_right (measure_singleton x)
  have hremovePos : volume (E \ {x}) ≠ 0 := by
    rw [hremove]
    exact hEpos
  obtain ⟨y, hyE, hyp⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hremovePos (ae_restrict_of_ae hp)
  have hyne : y ≠ x := hyE.2
  rcases lt_or_gt_of_ne hyne with hyx | hxy
  · exact ⟨y, x, hyE.1, hxE, hyx, hyp, hxp⟩
  · exact ⟨x, y, hxE, hyE.1, hxy, hxp, hyp⟩

end SpringerLean
