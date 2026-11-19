import SpringerLean.Round20ComparisonPotential

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- The actual rotated logarithmic boundary potential. -/
noncomputable def regularExteriorRotatedPotential
    (F : ℂ → ℂ) (s : ℝ) (ξ z : ℂ) : ℝ :=
  Real.circleAverage
    (fun ζ : ℂ => Real.log ‖z - conj ξ * rescaleExterior s F ζ‖) 0 1

/-- The comparison segment potential with the same circle normalization. -/
noncomputable def comparisonSegmentPotential (z : ℂ) : ℝ :=
  Real.circleAverage
    (fun ζ : ℂ => Real.log ‖z - ((2 * ζ.re : ℝ) : ℂ)‖) 0 1

/-- Bounded measurable sets of the required vertical length. -/
def verticalFeasible (h : ℝ) : Set (Set ℝ) :=
  {E | MeasurableSet E ∧ Bornology.IsBounded E ∧
    volume E = ENNReal.ofReal (2 * h)}

/-- Actual potential costs of feasible vertical sets. -/
noncomputable def regularVerticalCosts
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a h : ℝ) : Set ℝ :=
  {q | ∃ E ∈ verticalFeasible h,
    q = ∫ t in E,
      regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)}

/-- The finite vertical-interval version of the BLP auxiliary function.
Its boundary value at nonpositive height is explicitly the previously
verified full-line potential difference. -/
noncomputable def regularVerticalAuxiliary
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a h : ℝ) : ℝ :=
  if h ≤ 0 then
    ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ a t
  else
    (∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ a t) +
      (∫ t in Icc (-h) h,
        comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) -
      sInf (regularVerticalCosts F s ξ a h)

theorem regularVerticalAuxiliary_boundary
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a : ℝ) :
    regularVerticalAuxiliary F s ξ a 0 =
      ∫ t : ℝ, regularExteriorVerticalPotentialDifference F s ξ a t := by
  simp [regularVerticalAuxiliary]

theorem centered_interval_verticalFeasible (h t₀ : ℝ) :
    Icc (t₀ - h) (t₀ + h) ∈ verticalFeasible h := by
  refine ⟨measurableSet_Icc, isBounded_Icc _ _, ?_⟩
  rw [Real.volume_Icc]
  congr 1
  ring

theorem regularVerticalCosts_nonempty
    (F : ℂ → ℂ) (s : ℝ) (ξ : ℂ) (a h : ℝ) :
    (regularVerticalCosts F s ξ a h).Nonempty := by
  refine ⟨∫ t in Icc (-h) h,
      regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I), ?_⟩
  exact ⟨Icc ((0 : ℝ) - h) (0 + h), centered_interval_verticalFeasible h 0, by simp⟩

theorem regularVerticalCosts_bddBelow
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) :
    BddBelow (regularVerticalCosts F s ξ a h) := by
  refine ⟨0, ?_⟩
  rintro q ⟨E, _, rfl⟩
  exact integral_nonneg (fun t => by
    exact regularExterior_rotated_boundary_potential_nonneg
      F hc hs0 hs1 ξ hξ ((a : ℂ) + (t : ℂ) * Complex.I))

/-- The infimum is bounded above by the cost of any interval of the
prescribed length, without assuming an optimizer exists. -/
theorem regularVerticalCosts_sInf_le_centered_interval
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h t₀ : ℝ) :
    sInf (regularVerticalCosts F s ξ a h) ≤
      ∫ t in Icc (t₀ - h) (t₀ + h),
        regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I) := by
  apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h)
  exact ⟨Icc (t₀ - h) (t₀ + h),
    centered_interval_verticalFeasible h t₀, rfl⟩

/-- The boundary one-sided comparison obtained by inserting the interval
centered at a contact point into the actual cost infimum. -/
theorem regularVerticalAuxiliary_boundary_difference_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h t₀ : ℝ) (hh : 0 < h) :
    regularVerticalAuxiliary F s ξ a 0 -
      regularVerticalAuxiliary F s ξ a h ≤
        (∫ t in Icc (t₀ - h) (t₀ + h),
          regularExteriorRotatedPotential F s ξ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (∫ t in Icc (-h) h,
          comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [regularVerticalAuxiliary_boundary]
  simp only [regularVerticalAuxiliary, not_le.mpr hh, ↓reduceIte]
  have h := regularVerticalCosts_sInf_le_centered_interval
    F hc hs0 hs1 ξ hξ a h t₀
  linarith

end SpringerLean
