import SpringerLean.Round30ActualCircleIntegrable
import SpringerLean.Round30ComparisonClipEq

open MeasureTheory Set Metric Filter

namespace SpringerLean

/-- The comparison segment potential integrated over a bounded vertical set
outside height h is circle integrable whenever the radius is below h. -/
theorem comparisonSegmentPotential_vertical_set_circleIntegrable_of_sep
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a h ρ : ℝ) (hρ : 0 ≤ ρ) (hρh : ρ < h)
    (hsep : ∀ t ∈ E, h ≤ |t|) :
    CircleIntegrable
      (fun z : ℂ => ∫ t in E,
        comparisonSegmentPotential (z + (t : ℂ) * Complex.I))
      (a : ℂ) ρ := by
  let δ : ℝ := h - ρ
  have hδ : 0 < δ := sub_pos.mpr hρh
  let P : ℂ → ℝ := comparisonSegmentPotentialClipped δ
  have hP : Continuous P := comparisonSegmentPotentialClipped_continuous hδ
  let f : ℝ → ℂ → ℝ := fun t z => P (z + (t : ℂ) * Complex.I)
  have hf : Continuous (fun p : ℝ × ℂ => f p.1 p.2) :=
    hP.comp (by fun_prop)
  have hci : CircleIntegrable (fun z : ℂ => ∫ t in E, f t z)
      (a : ℂ) ρ := continuous_vertical_set_integral_circleIntegrable
        f hf E hEm hEb (a : ℂ) ρ
  have hcircle (t : ℝ) (ht : t ∈ E)
      (z : ℂ) (hz : z ∈ sphere (a : ℂ) |ρ|) :
      P (z + (t : ℂ) * Complex.I) =
        comparisonSegmentPotential (z + (t : ℂ) * Complex.I) := by
    apply comparisonSegmentPotentialClipped_eq_of_im
    have hrad : ‖z - (a : ℂ)‖ = ρ := by
      simpa [mem_sphere, dist_eq_norm, abs_of_nonneg hρ] using hz
    have him : |z.im| ≤ ρ := by
      have h := Complex.abs_im_le_norm (z - (a : ℂ))
      simpa [Complex.sub_im, hrad] using h
    have htri : |t| ≤ |t + z.im| + |z.im| := by
      calc
        |t| = |(t + z.im) - z.im| := by ring
        _ = |(t + z.im) + (-z.im)| := by ring
        _ ≤ |t + z.im| + |-z.im| := abs_add_le _ _
        _ = |t + z.im| + |z.im| := by rw [abs_neg]
    have hsum : (z + (t : ℂ) * Complex.I).im = z.im + t := by simp
    rw [hsum, add_comm]
    dsimp [δ]
    linarith [hsep t ht]
  apply CircleIntegrable.congr_codiscreteWithin ?_ hci
  filter_upwards [self_mem_codiscreteWithin (sphere (a : ℂ) |ρ|)] with z hz
  apply setIntegral_congr_fun hEm
  intro t ht
  exact hcircle t ht z hz

end SpringerLean