import SpringerLean.Round23Sublevel

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean

/-- A finite-mass threshold for a measurable coercive nonnegative real
function. The two inequalities allow an exact cut of its level set. -/
theorem measurable_sublevel_threshold
    (f : ℝ → ℝ) (hf : Measurable f) (hnonneg : ∀ t, 0 ≤ f t)
    (m : ℝ≥0∞) (hmpos : 0 < m)
    (hfinite : ∀ R : ℝ, volume {t : ℝ | f t ≤ R} ≠ ∞)
    (hmass : ∃ R : ℝ, m ≤ volume {t : ℝ | f t ≤ R}) :
    ∃ ell : ℝ,
      volume {t : ℝ | f t < ell} ≤ m ∧
      m ≤ volume {t : ℝ | f t ≤ ell} := by
  let S : Set ℝ := {R | m ≤ volume {t : ℝ | f t ≤ R}}
  have hSnonempty : S.Nonempty := hmass
  have hSbelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro R hR
    by_contra h
    have hRneg : R < 0 := lt_of_not_ge h
    have hempty : {t : ℝ | f t ≤ R} = ∅ := by
      ext t
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le hRneg (hnonneg t))
    change m ≤ volume {t : ℝ | f t ≤ R} at hR
    rw [hempty, measure_empty] at hR
    exact (not_le.mpr hmpos) hR
  let ell : ℝ := sInf S
  let lower : ℕ → Set ℝ := fun n => {t | f t ≤ ell - 1 / ((n : ℝ) + 1)}
  let upper : ℕ → Set ℝ := fun n => {t | f t ≤ ell + 1 / ((n : ℝ) + 1)}
  have hmono : Monotone lower := by
    intro n p hnp t ht
    change f t ≤ ell - 1 / ((n : ℝ) + 1) at ht
    change f t ≤ ell - 1 / ((p : ℝ) + 1)
    have hfrac : 1 / ((p : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnp 1
    linarith
  have hanti : Antitone upper := by
    intro n p hnp t ht
    change f t ≤ ell + 1 / ((p : ℝ) + 1) at ht
    change f t ≤ ell + 1 / ((n : ℝ) + 1)
    have hfrac : 1 / ((p : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnp 1
    linarith
  have hunion : (⋃ n, lower n) = {t : ℝ | f t < ell} := by
    ext t
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      change f t ≤ ell - 1 / ((n : ℝ) + 1) at hn
      linarith
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ht)
      refine ⟨n, ?_⟩
      change f t ≤ ell - 1 / ((n : ℝ) + 1)
      linarith
  have hinter : (⋂ n, upper n) = {t : ℝ | f t ≤ ell} := by
    ext t
    simp only [mem_iInter, mem_setOf_eq]
    constructor
    · intro ht
      by_contra h
      have hlt : ell < f t := lt_of_not_ge h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have htn := ht n
      change f t ≤ ell + 1 / ((n : ℝ) + 1) at htn
      linarith
    · intro ht n
      change f t ≤ ell + 1 / ((n : ℝ) + 1)
      have hpos : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith
  refine ⟨ell, ?_, ?_⟩
  · rw [← hunion, hmono.measure_iUnion]
    apply iSup_le
    intro n
    have hlt : ell - 1 / ((n : ℝ) + 1) < ell := by
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hnot := notMem_of_lt_csInf hlt hSbelow
    have hnot' : ¬ m ≤ volume (lower n) := hnot
    exact le_of_lt (lt_of_not_ge hnot')
  · rw [← hinter, hanti.measure_iInter]
    · apply le_iInf
      intro n
      have hlt : ell < ell + 1 / ((n : ℝ) + 1) := by
        have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨R, hRS, hRlt⟩ := exists_lt_of_csInf_lt hSnonempty hlt
      exact hRS.trans (measure_mono (by
        intro t ht
        exact le_trans ht hRlt.le))
    · intro n
      exact (hf measurableSet_Iic).nullMeasurableSet
    · exact ⟨0, hfinite _⟩

/-- The actual regularized vertical potential has a finite mass quantile
for every positive prescribed height. -/
theorem regularExterior_vertical_threshold
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (a h : ℝ) (hh : 0 < h) :
    ∃ ell : ℝ,
      volume {t : ℝ | regularExteriorRotatedPotential F s ξ
        ((a : ℂ) + (t : ℂ) * Complex.I) < ell} ≤ ENNReal.ofReal (2 * h) ∧
      ENNReal.ofReal (2 * h) ≤
        volume {t : ℝ | regularExteriorRotatedPotential F s ξ
          ((a : ℂ) + (t : ℂ) * Complex.I) ≤ ell} := by
  let f : ℝ → ℝ := fun t => regularExteriorRotatedPotential F s ξ
    ((a : ℂ) + (t : ℂ) * Complex.I)
  have hline : Measurable (fun t : ℝ =>
      (a : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hf : Measurable f :=
    (regularExterior_rotated_potential_measurable F hc hs0 hs1 ξ hξ).comp hline
  apply measurable_sublevel_threshold f hf
  · intro t
    exact regularExterior_rotated_boundary_potential_nonneg
      F hc hs0 hs1 ξ hξ _
  · exact ENNReal.ofReal_pos.mpr (by linarith)
  · intro R
    exact (regularExterior_vertical_sublevel_measurable_bounded
      F hc hs0 hs1 ξ hξ a R).2.measure_lt_top.ne
  · exact regularExterior_vertical_sublevel_mass_ge
      F hc hs0 hs1 ξ hξ a h

end SpringerLean
