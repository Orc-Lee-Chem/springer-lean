import SpringerLean.Round28CostDifference

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- The actual minimum vertical cost is uniformly continuous in the
horizontal coordinate on each bounded rectangle with positive heights. -/
theorem regularVerticalCosts_inf_uniform_horizontal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (a b h : ℝ), |a| ≤ A → |b| ≤ A → 0 < h → h ≤ H →
        |a - b| < δ →
          |sInf (regularVerticalCosts F s ξ a h) -
            sInf (regularVerticalCosts F s ξ b h)| < ε := by
  obtain ⟨T, hT, hmin⟩ :=
    regularVerticalCosts_exists_minimizer_uniform_window
      F hc hs0 hs1 ξ hξ A H hA hH
  intro ε hε
  let η : ℝ := ε / (2 * H + 1)
  have hden : 0 < 2 * H + 1 := by linarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hstrip⟩ :=
    regularExterior_rotated_potential_uniform_horizontal_on_strip
      F hc hs0 hs1 ξ hξ A T hA hT η hη
  refine ⟨δ, hδ, ?_⟩
  intro a b h ha hb hh hHh hab
  let f : ℝ → ℝ → ℝ := fun x t =>
    regularExteriorRotatedPotential F s ξ ((x : ℂ) + (t : ℂ) * Complex.I)
  let m : ℝ → ℝ := fun x => sInf (regularVerticalCosts F s ξ x h)
  have hcost (E : Set ℝ) (hE : E ∈ verticalFeasible h)
      (hET : E ⊆ Icc (-T) T) :
      |(∫ t in E, f a t) - (∫ t in E, f b t)| ≤ η * (2 * h) := by
    have hEfin : volume E ≠ ∞ := by
      rw [hE.2.2]
      finiteness
    have hEa := regularExterior_vertical_cost_integrableOn
      F hc hs0 hs1 ξ hξ a h E hE
    have hEb := regularExterior_vertical_cost_integrableOn
      F hc hs0 hs1 ξ hξ b h E hE
    have hpoint : ∀ t ∈ E, |f a t - f b t| ≤ η := by
      intro t ht
      have htT : |t| ≤ T := abs_le.mpr (hET ht)
      exact le_of_lt (hstrip a b t ha hb htT hab)
    have hbase := abs_setIntegral_sub_le_of_uniform_bound E hE.1 hEfin
      (f a) (f b) hEa hEb η hη.le hpoint
    have hmass : volume.real E = 2 * h := by
      rw [Measure.real_def, hE.2.2, ENNReal.toReal_ofReal (by linarith)]
    simpa only [hmass] using hbase
  obtain ⟨Ea, hEa, hEaT, hEaEq⟩ := hmin a h ha hh hHh
  obtain ⟨Eb, hEb, hEbT, hEbEq⟩ := hmin b h hb hh hHh
  have hba : m b ≤ ∫ t in Ea, f b t := by
    apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ b h)
    exact ⟨Ea, hEa, rfl⟩
  have hab' : m a ≤ ∫ t in Eb, f a t := by
    apply csInf_le (regularVerticalCosts_bddBelow F hc hs0 hs1 ξ hξ a h)
    exact ⟨Eb, hEb, rfl⟩
  have hEaDiff := hcost Ea hEa hEaT
  have hEbDiff := hcost Eb hEb hEbT
  have hma : (∫ t in Ea, f a t) = m a := hEaEq
  have hmb : (∫ t in Eb, f b t) = m b := hEbEq
  have hbound : |m a - m b| ≤ η * (2 * h) := by
    apply abs_le.mpr
    constructor
    · have hEaLower := (abs_le.mp hEaDiff).1
      rw [hma] at hEaLower
      linarith
    · have hEbUpper := (abs_le.mp hEbDiff).2
      rw [hmb] at hEbUpper
      linarith
  have htarget : η * (2 * h) < ε := by
    have hratio : η * (2 * H + 1) = ε := by
      dsimp [η]
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left hHh hη.le]
  exact lt_of_le_of_lt hbound htarget

end SpringerLean