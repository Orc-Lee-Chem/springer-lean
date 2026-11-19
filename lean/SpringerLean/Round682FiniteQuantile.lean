import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- A finite-measure version of the threshold construction. A lower
bound replaces the nonnegative/coercive hypotheses of the vertical-line
construction. No topology or assertion about interiors of levels is used. -/
theorem finiteMeasure_sublevel_threshold
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hbelow : ∀ x, C ≤ f x)
    (m : ℝ≥0∞) (hmpos : 0 < m)
    (hmass : ∃ R : ℝ, m ≤ μ {x | f x ≤ R}) :
    ∃ ell : ℝ, μ {x | f x < ell} ≤ m ∧ m ≤ μ {x | f x ≤ ell} := by
  let S : Set ℝ := {R | m ≤ μ {x | f x ≤ R}}
  have hSnonempty : S.Nonempty := hmass
  have hSbelow : BddBelow S := by
    refine ⟨C, ?_⟩
    intro R hR
    by_contra h
    have hRlt : R < C := lt_of_not_ge h
    have hempty : {x : α | f x ≤ R} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      exact not_le.mpr (lt_of_lt_of_le hRlt (hbelow x))
    change m ≤ μ {x | f x ≤ R} at hR
    rw [hempty, measure_empty] at hR
    exact (not_le.mpr hmpos) hR
  let ell : ℝ := sInf S
  let lower : ℕ → Set α := fun n => {x | f x ≤ ell - 1 / ((n : ℝ) + 1)}
  let upper : ℕ → Set α := fun n => {x | f x ≤ ell + 1 / ((n : ℝ) + 1)}
  have hmono : Monotone lower := by
    intro n p hnp x hx
    change f x ≤ ell - 1 / ((n : ℝ) + 1) at hx
    change f x ≤ ell - 1 / ((p : ℝ) + 1)
    have hfrac : 1 / ((p : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnp 1
    linarith
  have hanti : Antitone upper := by
    intro n p hnp x hx
    change f x ≤ ell + 1 / ((p : ℝ) + 1) at hx
    change f x ≤ ell + 1 / ((n : ℝ) + 1)
    have hfrac : 1 / ((p : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnp 1
    linarith
  have hunion : (⋃ n, lower n) = {x : α | f x < ell} := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      change f x ≤ ell - 1 / ((n : ℝ) + 1) at hn
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      refine ⟨n, ?_⟩
      change f x ≤ ell - 1 / ((n : ℝ) + 1)
      linarith
  have hinter : (⋂ n, upper n) = {x : α | f x ≤ ell} := by
    ext x
    simp only [mem_iInter, mem_setOf_eq]
    constructor
    · intro hx
      by_contra h
      have hlt : ell < f x := lt_of_not_ge h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have hxn := hx n
      change f x ≤ ell + 1 / ((n : ℝ) + 1) at hxn
      linarith
    · intro hx n
      change f x ≤ ell + 1 / ((n : ℝ) + 1)
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
    have hnot' : ¬ m ≤ μ (lower n) := hnot
    exact le_of_lt (lt_of_not_ge hnot')
  · rw [← hinter, hanti.measure_iInter]
    · apply le_iInf
      intro n
      have hlt : ell < ell + 1 / ((n : ℝ) + 1) := by
        have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      obtain ⟨R, hRS, hRlt⟩ := exists_lt_of_csInf_lt hSnonempty hlt
      exact hRS.trans (measure_mono (by
        intro x hx
        exact le_trans hx hRlt.le))
    · intro n
      exact (hf measurableSet_Iic).nullMeasurableSet
    · exact ⟨0, measure_ne_top μ _⟩

/-- Null levels make the threshold's mass exact. This is the only use
of the null-level hypothesis; positive measure is never turned into an
interior-point assertion. -/
theorem finiteMeasure_exists_strict_sublevel_mass_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hbelow : ∀ x, C ≤ f x)
    (hlevels : ∀ c : ℝ, μ {x | f x = c} = 0)
    (m : ℝ≥0∞) (hmpos : 0 < m)
    (hmass : ∃ R : ℝ, m ≤ μ {x | f x ≤ R}) :
    ∃ ell : ℝ, μ {x | f x < ell} = m := by
  obtain ⟨ell, hl, hu⟩ := finiteMeasure_sublevel_threshold μ f hf C hbelow m hmpos hmass
  have hne : ∀ᵐ x ∂μ, f x ≠ ell := by
    apply ae_iff.mpr
    simpa only [ne_eq, not_not] using hlevels ell
  have heq : {x | f x ≤ ell} =ᵐ[μ] {x | f x < ell} := by
    filter_upwards [hne] with x hx
    simp only [mem_setOf_eq, le_iff_lt_or_eq, hx, or_false]
  have hmeasure := measure_congr heq
  exact ⟨ell, le_antisymm hl (by rwa [← hmeasure])⟩

/-- A bounded-above variable with null levels has a strict top level
of every positive mass for which a threshold candidate exists. -/
theorem finiteMeasure_exists_strict_superlevel_mass_eq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (B : ℝ) (habove : ∀ x, f x ≤ B)
    (hlevels : ∀ c : ℝ, μ {x | f x = c} = 0)
    (m : ℝ≥0∞) (hmpos : 0 < m)
    (hmass : ∃ R : ℝ, m ≤ μ {x | -f x ≤ R}) :
    ∃ ell : ℝ, μ {x | ell < f x} = m := by
  have hneg : ∀ c : ℝ, μ {x | -f x = c} = 0 := by
    intro c
    have heq : {x | -f x = c} = {x | f x = -c} := by
      ext x
      simp only [mem_setOf_eq]
      constructor <;> intro h <;> linarith
    rw [heq]
    exact hlevels (-c)
  obtain ⟨ell, he⟩ := finiteMeasure_exists_strict_sublevel_mass_eq μ
    (fun x => -f x) hf.neg (-B) (fun x => by linarith [habove x])
    hneg m hmpos hmass
  refine ⟨-ell, ?_⟩
  have hset : {x : α | -ell < f x} = {x : α | -f x < ell} := by
    ext x
    simp only [mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact he

end SpringerLean
