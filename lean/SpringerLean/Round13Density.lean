import SpringerLean.Round13DensityPrelude
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory Metric Set

namespace SpringerLean

noncomputable def comparisonDiskReDensity (x : ℝ) : ENNReal :=
  if |x| < 1 then ENNReal.ofReal (2 * Real.sqrt (1 - x ^ 2)) else 0

/-- The real-coordinate projection of unnormalized disk area has the
vertical-section density `2 sqrt(1-x²)` on `|x|<1`. -/
theorem comparisonDisk_re_pushforward_density :
    Measure.map (fun z : ℂ => z.re)
      (volume.restrict (ball (0 : ℂ) 1)) =
    (volume : Measure ℝ).withDensity comparisonDiskReDensity := by
  apply Measure.ext
  intro B hB
  have hMk : Measurable (fun p : ℝ × ℝ => Complex.mk p.1 p.2) := by
    convert Complex.measurableEquivRealProd.symm.measurable using 1
    funext p
    exact (Complex.measurableEquivRealProd_symm_apply p).symm
  have hS : MeasurableSet
      {p : ℝ × ℝ | Complex.mk p.1 p.2 ∈ ball (0 : ℂ) 1 ∧ p.1 ∈ B} :=
    (isOpen_ball.measurableSet.preimage hMk).inter (hB.preimage measurable_fst)
  have hC : ((fun z : ℂ => z.re) ⁻¹' B) ∩ ball (0 : ℂ) 1 =
      Complex.measurableEquivRealProd ⁻¹'
        {p : ℝ × ℝ | Complex.mk p.1 p.2 ∈ ball (0 : ℂ) 1 ∧ p.1 ∈ B} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq,
      Complex.measurableEquivRealProd_apply]
    constructor <;> intro h
    · exact ⟨by simpa using h.2, h.1⟩
    · exact ⟨h.2, by simpa using h.1⟩
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.restrict_apply (by measurability), hC,
    Complex.volume_preserving_equiv_real_prod.measure_preimage hS.nullMeasurableSet,
    Measure.volume_eq_prod ℝ ℝ, Measure.prod_apply hS,
    withDensity_apply comparisonDiskReDensity hB]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro x
  change (volume : Measure ℝ)
      {y : ℝ | Complex.mk x y ∈ ball (0 : ℂ) 1 ∧ x ∈ B} =
    B.indicator comparisonDiskReDensity x
  by_cases hxB : x ∈ B
  · simp only [hxB, and_true, Set.indicator_of_mem]
    by_cases hx : |x| < 1
    · simpa [comparisonDiskReDensity, hx] using comparisonDisk_vertical_section_volume x hx
    · have hge : 1 ≤ |x| := le_of_not_gt hx
      change (volume : Measure ℝ) {y : ℝ | Complex.mk x y ∈ ball (0 : ℂ) 1} =
        comparisonDiskReDensity x
      rw [comparisonDisk_vertical_section_empty x hge]
      simp [comparisonDiskReDensity, hx]
  · have hleft : {y : ℝ | Complex.mk x y ∈ ball (0 : ℂ) 1 ∧ x ∈ B} = ∅ := by
      ext y
      simp [hxB]
    rw [hleft]
    simp [Set.indicator, hxB]

end SpringerLean