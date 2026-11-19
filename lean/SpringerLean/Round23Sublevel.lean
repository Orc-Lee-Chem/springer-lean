import SpringerLean.Round23MeasureCut

open MeasureTheory Set Metric
open scoped ENNReal ComplexConjugate

namespace SpringerLean

/-- The actual vertical potential is measurable, and each of its finite
sublevel sets is bounded. This is the compactness input for the bathtub
construction of a minimizing set. -/
theorem regularExterior_vertical_sublevel_measurable_bounded
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a R : ℝ) :
    MeasurableSet {t : ℝ |
      regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) ≤ R} ∧
      Bornology.IsBounded {t : ℝ |
        regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I) ≤ R} := by
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hline : Measurable (fun t : ℝ =>
      (a : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hf : Measurable f :=
    (regularExterior_rotated_potential_measurable F hc hs0 hs1 ξ hξ).comp hline
  obtain ⟨T, hT0, hT⟩ :=
    regularExterior_rotated_potential_vertical_coercive
      F hc hs0 hs1 ξ hξ a (R + 1)
  constructor
  · exact hf (measurableSet_Iic)
  · apply (Metric.isBounded_iff_subset_closedBall 0).2
    refine ⟨T, ?_⟩
    intro t ht
    have hsmall : |t| < T := by
      by_contra h
      have hlarge := hT t (le_of_not_gt h)
      change regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) ≤ R at ht
      linarith
    simpa [Real.dist_eq, abs_sub_comm] using le_of_lt hsmall

/-- Every positive prescribed vertical length fits into one finite sublevel
set of the actual regularized potential. -/
theorem regularExterior_vertical_sublevel_mass_ge
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) :
    ∃ R : ℝ, ENNReal.ofReal (2 * h) ≤
      volume {t : ℝ | regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) ≤ R} := by
  obtain ⟨C, hC0, hC⟩ :=
    regularExterior_boundary_potential_linear_bound F hc hs0 hs1
  let R : ℝ := |a| + h + C + 1
  refine ⟨R, ?_⟩
  have hsubset : Icc (-h) h ⊆
      {t : ℝ | regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) ≤ R} := by
    intro t ht
    have hrot := regularExterior_rotated_potential_eq F s ξ hξ
      ((a : ℂ) + (t : ℂ) * Complex.I)
    have hupper := hC (ξ * ((a : ℂ) + (t : ℂ) * Complex.I))
    rw [← hrot, norm_mul, hξ, one_mul] at hupper
    have hlinebound : ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤ |a| + |t| := by
      calc
        ‖(a : ℂ) + (t : ℂ) * Complex.I‖ ≤
            ‖(a : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |a| + |t| := by simp
    have htbound : |t| ≤ h := abs_le.mpr ht
    change regularExteriorRotatedPotential F s ξ
      ((a : ℂ) + (t : ℂ) * Complex.I) ≤ R
    dsimp [R]
    linarith
  calc
    ENNReal.ofReal (2 * h) = volume (Icc (-h) h) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    _ ≤ _ := measure_mono hsubset

end SpringerLean
