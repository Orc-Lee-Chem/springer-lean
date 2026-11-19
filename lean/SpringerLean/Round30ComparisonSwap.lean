import SpringerLean.Round30ComparisonClipEq

open MeasureTheory Set Metric

namespace SpringerLean

/-- On a bounded vertical set separated from the real segment by more than
the circle radius, the actual comparison potential commutes with circle
averaging and vertical integration. The proof clips the singular kernel only
outside the region being integrated. -/
theorem comparisonSegmentPotential_vertical_circle_swap_of_sep
    (E : Set ℝ) (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a h ρ : ℝ) (hρ : 0 ≤ ρ) (hρh : ρ < h)
    (hsep : ∀ t ∈ E, h ≤ |t|) :
    (∫ t in E, Real.circleAverage
      (fun z : ℂ => comparisonSegmentPotential (z + (t : ℂ) * Complex.I))
      (a : ℂ) ρ) =
    Real.circleAverage
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
  have hswap := setIntegral_circleAverage_swap_of_continuous
    f hf E hEm hEb (a : ℂ) ρ
  have hcenter (t : ℝ) (ht : t ∈ E) :
      P ((a : ℂ) + (t : ℂ) * Complex.I) =
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I) := by
    apply comparisonSegmentPotentialClipped_eq_of_im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      zero_mul, mul_one, zero_add, add_zero]
    dsimp [δ]
    linarith [hsep t ht]
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
  have hleft :
      (∫ t in E, Real.circleAverage
        (fun z : ℂ => comparisonSegmentPotential (z + (t : ℂ) * Complex.I))
        (a : ℂ) ρ) =
      ∫ t in E, Real.circleAverage (f t) (a : ℂ) ρ := by
    apply setIntegral_congr_fun hEm
    intro t ht
    apply Real.circleAverage_congr_sphere
    intro z hz
    exact (hcircle t ht z hz).symm
  have hright :
      Real.circleAverage (fun z : ℂ => ∫ t in E,
        comparisonSegmentPotential (z + (t : ℂ) * Complex.I))
        (a : ℂ) ρ =
      Real.circleAverage (fun z : ℂ => ∫ t in E, f t z) (a : ℂ) ρ := by
    apply Real.circleAverage_congr_sphere
    intro z hz
    apply setIntegral_congr_fun hEm
    intro t ht
    exact (hcircle t ht z hz).symm
  rw [hleft, hright]
  exact hswap

end SpringerLean
