import SpringerLean.Round28ComparisonHeight
import SpringerLean.Round28CostDifference
import SpringerLean.Round27TailL1

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- Uniform horizontal continuity of the comparison integral for bounded heights. -/
theorem comparisonSegmentPotential_interval_integral_uniform_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (a b h : ℝ), |a| ≤ A → |b| ≤ A → 0 ≤ h → h ≤ H →
        |a - b| < δ →
        |(∫ t in Icc (-h) h,
            comparisonSegmentPotential ((a : ℂ) + (t : ℂ) * Complex.I)) -
          (∫ t in Icc (-h) h,
            comparisonSegmentPotential ((b : ℂ) + (t : ℂ) * Complex.I))| < ε := by
  intro ε hε
  let η : ℝ := ε / (4 * H + 1)
  have hdenH : 0 < 4 * H + 1 := by linarith
  have hη : 0 < η := div_pos hε hdenH
  obtain ⟨δ₁, hδ₁, hstrip⟩ :=
    regularExterior_rotated_potential_uniform_horizontal_on_strip
      F hc hs0 hs1 ξ hξ A H hA hH η hη
  let δ : ℝ := min δ₁ (ε / (4 * Real.pi + 1))
  have hdenPi : 0 < 4 * Real.pi + 1 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro a b h ha hb hh hHh hab
  have hδ₁' : δ ≤ δ₁ := min_le_left _ _
  have hδ₂' : δ ≤ ε / (4 * Real.pi + 1) := min_le_right _ _
  let S : Set ℝ := Icc (-h) h
  let g : ℝ → ℝ → ℝ := fun x t =>
    regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I)
  let d : ℝ → ℝ → ℝ := fun x t => regularExteriorVerticalPotentialDifference F s ξ x t
  have hS : S ∈ verticalFeasible h := by
    simpa [S] using centered_interval_verticalFeasible h 0
  have hSfin : volume S ≠ ∞ := by rw [hS.2.2]; finiteness
  have hSreal : volume.real S = 2 * h := by
    rw [Measure.real_def, hS.2.2, ENNReal.toReal_ofReal (by linarith)]
  have hga := regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ a h S hS
  have hgb := regularExterior_vertical_cost_integrableOn F hc hs0 hs1 ξ hξ b h S hS
  have hda := (regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a).integrableOn (s := S)
  have hdb := (regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ b).integrableOn (s := S)
  have hpoint : ∀ t ∈ S, |g a t - g b t| ≤ η := by
    intro t ht
    have htT : |t| ≤ H := by
      have := abs_le.mpr ht
      linarith
    exact le_of_lt (hstrip a b t ha hb htT (lt_of_lt_of_le hab hδ₁'))
  have hgdiff := abs_setIntegral_sub_le_of_uniform_bound S hS.1 hSfin
    (g a) (g b) hga hgb η hη.le hpoint
  rw [hSreal] at hgdiff
  have hddiff := regularExterior_vertical_difference_setIntegral_lipschitz_horizontal
    F hc hs0 hs1 ξ S a b
  have hEq (x : ℝ) (hdx : IntegrableOn (g x) S)
      (hddx : IntegrableOn (d x) S) :
      (∫ t in S, comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I)) =
        (∫ t in S, g x t) - (∫ t in S, d x t) := by
    have halg (t : ℝ) :
        comparisonSegmentPotential ((x : ℂ) + (t : ℂ) * Complex.I) =
        g x t - d x t := by
      dsimp [g, d, regularExteriorVerticalPotentialDifference,
        regularExteriorRotatedPotential, comparisonSegmentPotential]
      ring
    simp_rw [halg]
    exact integral_sub hdx hddx
  rw [show Icc (-h) h = S from rfl, hEq a hga hda, hEq b hgb hdb]
  have hηeq : η * (4 * H + 1) = ε := by dsimp [η]; field_simp
  have hδeq : (ε / (4 * Real.pi + 1)) * (4 * Real.pi + 1) = ε := by field_simp
  have hactual : η * (2 * h) < ε / 2 := by
    have := mul_le_mul_of_nonneg_left hHh hη.le
    nlinarith [hηeq]
  have hcomparison : 2 * Real.pi * |a - b| < ε / 2 := by
    have := mul_lt_mul_of_pos_left (lt_of_lt_of_le hab hδ₂')
      (by positivity : 0 < 2 * Real.pi)
    nlinarith [hδeq]
  have htri := abs_add_le
    ((∫ t in S, g a t) - (∫ t in S, g b t))
    (-((∫ t in S, d a t) - (∫ t in S, d b t)))
  have htri' :
      |((∫ t in S, g a t) - (∫ t in S, d a t)) -
        ((∫ t in S, g b t) - (∫ t in S, d b t))| ≤
      |(∫ t in S, g a t) - (∫ t in S, g b t)| +
      |(∫ t in S, d a t) - (∫ t in S, d b t)| := by
    calc
      _ = |((∫ t in S, g a t) - (∫ t in S, g b t)) +
          -((∫ t in S, d a t) - (∫ t in S, d b t))| := by ring
      _ ≤ _ := by simpa only [abs_neg] using htri
  have hsum :
      |(∫ t in S, g a t) - (∫ t in S, g b t)| +
      |(∫ t in S, d a t) - (∫ t in S, d b t)| < ε := by
    linarith
  exact lt_of_le_of_lt htri' hsum
end SpringerLean