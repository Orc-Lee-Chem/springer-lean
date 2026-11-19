import SpringerLean.Round30ComplexVerticalBridge
import SpringerLean.Round30ComparisonClipEq

open MeasureTheory Set Metric

namespace SpringerLean

/-- The comparison logarithmic potential is integrable over any bounded
vertical set separated from its real segment by a positive margin. -/
theorem comparisonSegmentPotential_vertical_set_integrableOn_of_sep
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (z : ℂ) (h ρ : ℝ) (hρ : 0 ≤ ρ) (hρh : ρ < h)
    (hz : |z.im| ≤ ρ) (hsep : ∀ t ∈ E, h ≤ |t|) :
    IntegrableOn
      (fun t : ℝ => comparisonSegmentPotential
        (z + (t : ℂ) * Complex.I)) E := by
  let δ : ℝ := h - ρ
  have hδ : 0 < δ := sub_pos.mpr hρh
  let P : ℂ → ℝ := comparisonSegmentPotentialClipped δ
  have hP : Continuous P := comparisonSegmentPotentialClipped_continuous hδ
  have hPc : Continuous (fun t : ℝ => P (z + (t : ℂ) * Complex.I)) :=
    hP.comp (by fun_prop)
  have hPint : IntegrableOn
      (fun t : ℝ => P (z + (t : ℂ) * Complex.I)) E :=
    (hPc.continuousOn.integrableOn_compact hEb.isCompact_closure).mono_set
      subset_closure
  apply IntegrableOn.congr_fun hPint ?_ hEm
  intro t ht
  apply comparisonSegmentPotentialClipped_eq_of_im
  have hsum : (z + (t : ℂ) * Complex.I).im = z.im + t := by simp
  rw [hsum]
  have htri : |t| ≤ |z.im + t| + |z.im| := by
    calc
      |t| = |(z.im + t) - z.im| := by ring
      _ ≤ |z.im + t| + |z.im| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (z.im + t) (-z.im))
  dsimp [δ]
  linarith [hsep t ht]

end SpringerLean