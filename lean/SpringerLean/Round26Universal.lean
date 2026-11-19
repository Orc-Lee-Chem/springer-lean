import SpringerLean.Round26FilledInterval

open MeasureTheory Set Filter
open scoped Topology ENNReal Classical

namespace SpringerLean

/-- Every bounded measurable positive-mass real set loses at least the
translation length under all sufficiently small positive right shifts. -/
theorem bounded_measurable_shift_sdiff_lower
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (hEpos : 0 < volume.real E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℝ, 0 < d → d < δ →
      d ≤ volume.real (E \ verticalShiftPlus E d) := by
  by_cases hgap : ∀ a b : ℝ, a < b →
      0 < volume.real (Ioo a b \ E)
  · exact realSet_shift_sdiff_lower_of_no_ae_interval E hE hEb hEpos hgap
  · push_neg at hgap
    obtain ⟨a, b, hab, hnonpos⟩ := hgap
    have hSb : Bornology.IsBounded (Ioo a b \ E) :=
      (Metric.isBounded_Ioo a b).subset sdiff_subset
    have hzeroReal : volume.real (Ioo a b \ E) = 0 := by
      have hnonneg : 0 ≤ volume.real (Ioo a b \ E) := measureReal_nonneg
      exact le_antisymm hnonpos hnonneg
    have hzero : volume (Ioo a b \ E) = 0 :=
      (measureReal_eq_zero_iff hSb.measure_lt_top.ne).mp hzeroReal
    exact realSet_shift_sdiff_lower_of_ae_filled_interval
      E hE hEb a b hab hzero

/-- The exact Round26 goal: the direction and factor two match the
project's vertical shifts. The case `ε=0` is included. -/
theorem bounded_measurable_verticalShift_diff_lower
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (hEpos : 0 < volume.real E) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
      2 * ε ≤ volume.real
        (verticalShiftPlus E ε \ verticalShiftMinus E ε) := by
  obtain ⟨D, hD, hbound⟩ :=
    bounded_measurable_shift_sdiff_lower E hE hEb hEpos
  refine ⟨D / 2, by positivity, ?_⟩
  intro ε hε0 hεD
  by_cases hε : ε = 0
  · subst ε
    simpa using (measureReal_nonneg :
      0 ≤ volume.real (verticalShiftPlus E 0 \ verticalShiftMinus E 0))
  · have hεpos : 0 < ε := lt_of_le_of_ne hε0 (Ne.symm hε)
    have h2εpos : 0 < 2 * ε := by linarith
    have h2εD : 2 * ε < D := by linarith
    rw [verticalShiftPlus_sdiff_verticalShiftMinus_measureReal E hE hEb ε]
    exact hbound (2 * ε) h2εpos h2εD

/-- The Round24 mass-splitting premise is now discharged for every
positive-height feasible set, using one radius for every smaller shift. -/
theorem verticalFeasible_shift_redistribute
    (E : Set ℝ) (h : ℝ) (hE : E ∈ verticalFeasible h)
    (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
      ∃ A ∈ verticalFeasible (h + ε),
        ∃ B ∈ verticalFeasible (h - ε),
          ∀ t : ℝ,
            (if t ∈ A then (1 : ℕ) else 0) +
              (if t ∈ B then (1 : ℕ) else 0) =
            (if t ∈ verticalShiftMinus E ε then (1 : ℕ) else 0) +
              (if t ∈ verticalShiftPlus E ε then (1 : ℕ) else 0) := by
  have hEmeas := hE.1
  have hEb := hE.2.1
  have hEmass := hE.2.2
  have hEpos : 0 < volume.real E := by
    rw [Measure.real_def, hEmass, ENNReal.toReal_ofReal (by linarith)]
    linarith
  obtain ⟨D, hD, hbound⟩ :=
    bounded_measurable_verticalShift_diff_lower E hEmeas hEb hEpos
  refine ⟨min D h, lt_min hD hh, ?_⟩
  intro ε hε0 hεδ
  exact verticalFeasible_shift_redistribute_of_diff_mass E h hE ε hε0
    (hεδ.trans_le (min_le_right _ _))
    (hbound ε hε0 (hεδ.trans_le (min_le_left _ _)))

/-- The same actual minimizing vertical set, with one uniform shift radius,
works for every smaller angle-dependent translation in the circle argument. -/
theorem regularVerticalCosts_exists_shiftable_minimizer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ E ∈ verticalFeasible h,
      (∫ t in E, regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
        sInf (regularVerticalCosts F s ξ a h) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
        ∃ A ∈ verticalFeasible (h + ε),
          ∃ B ∈ verticalFeasible (h - ε),
            ∀ t : ℝ,
              (if t ∈ A then (1 : ℕ) else 0) +
                (if t ∈ B then (1 : ℕ) else 0) =
              (if t ∈ verticalShiftMinus E ε then (1 : ℕ) else 0) +
                (if t ∈ verticalShiftPlus E ε then (1 : ℕ) else 0) := by
  obtain ⟨E, hE, hmin⟩ :=
    regularVerticalCosts_exists_minimizer F hc hs0 hs1 ξ hξ a h hh
  obtain ⟨δ, hδ, hsplit⟩ := verticalFeasible_shift_redistribute E h hE hh
  exact ⟨E, hE, hmin, δ, hδ, hsplit⟩

end SpringerLean
