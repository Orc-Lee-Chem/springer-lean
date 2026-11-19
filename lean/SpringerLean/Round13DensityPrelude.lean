import SpringerLean.Round13JensenPrelude
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open MeasureTheory Metric Set

namespace SpringerLean

/-- A horizontal slice of the open unit disk in real coordinates. -/
theorem comparisonDisk_horizontal_slice (x y : ℝ) (hx : |x| < 1) :
    Complex.mk x y ∈ ball (0 : ℂ) 1 ↔
      y ∈ Ioo (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2)) := by
  have hpos : 0 < 1 - x ^ 2 := by
    have h1 : -1 < x := (abs_lt.mp hx).1
    have h2 : x < 1 := (abs_lt.mp hx).2
    nlinarith
  have hsqrt : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hpos)
  rw [mem_ball, dist_zero_right]
  have hnorm : ‖Complex.mk x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply]
    ring
  constructor
  · intro h
    have hsq : ‖Complex.mk x y‖ ^ 2 < 1 := by nlinarith [norm_nonneg (Complex.mk x y)]
    change -Real.sqrt (1 - x ^ 2) < y ∧ y < Real.sqrt (1 - x ^ 2)
    have hsqrtpos : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    constructor
    · by_contra hn
      push_neg at hn
      have hp : 0 ≤ (y + Real.sqrt (1 - x ^ 2)) * (y - Real.sqrt (1 - x ^ 2)) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith
    · by_contra hn
      push_neg at hn
      have hp : 0 ≤ (y - Real.sqrt (1 - x ^ 2)) * (y + Real.sqrt (1 - x ^ 2)) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
  · intro h
    change -Real.sqrt (1 - x ^ 2) < y ∧ y < Real.sqrt (1 - x ^ 2) at h
    have hsqrtpos : 0 ≤ Real.sqrt (1 - x ^ 2) := Real.sqrt_nonneg _
    have hsq : x ^ 2 + y ^ 2 < 1 := by nlinarith
    nlinarith [norm_nonneg (Complex.mk x y)]


/-- The vertical section of the unit disk has length twice the semicircle
height. This is the Fubini input for the projected disk law. -/
theorem comparisonDisk_vertical_section_volume (x : ℝ) (hx : |x| < 1) :
    (volume : Measure ℝ) {y : ℝ | Complex.mk x y ∈ ball (0 : ℂ) 1} =
      ENNReal.ofReal (2 * Real.sqrt (1 - x ^ 2)) := by
  have hset : {y : ℝ | Complex.mk x y ∈ ball (0 : ℂ) 1} =
      Ioo (-Real.sqrt (1 - x ^ 2)) (Real.sqrt (1 - x ^ 2)) := by
    ext y
    exact comparisonDisk_horizontal_slice x y hx
  rw [hset, Real.volume_Ioo]
  congr 1
  ring

/-- A vertical section outside the horizontal unit interval is empty. -/
theorem comparisonDisk_vertical_section_empty (x : ℝ) (hx : 1 ≤ |x|) :
    {y : ℝ | Complex.mk x y ∈ ball (0 : ℂ) 1} = ∅ := by
  ext y
  simp only [mem_setOf_eq, mem_ball, dist_zero_right, mem_empty_iff_false, iff_false]
  intro h
  have hnorm : ‖Complex.mk x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply]
    ring
  have hxsq : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  nlinarith [sq_nonneg y, norm_nonneg (Complex.mk x y)]
end SpringerLean