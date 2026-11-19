import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Finset

namespace SpringerLean

/-- A finite tagged-sum estimate, proved directly from one-dimensional
interval integrals.  No general weak-convergence or box-integration
infrastructure is needed for the Chebyshev midpoint limit. -/
theorem tagged_interval_sum_error
    (f : ℝ → ℝ) (a tag : ℕ → ℝ) (n : ℕ) (ε : ℝ)
    (horder : ∀ i < n, a i ≤ a (i + 1))
    (hint : ∀ i < n, IntervalIntegrable f volume (a i) (a (i + 1)))
    (hosc : ∀ i < n, ∀ x ∈ Set.Icc (a i) (a (i + 1)), |f (tag i) - f x| ≤ ε) :
    |(∑ i ∈ range n, (a (i + 1) - a i) * f (tag i)) -
        ∫ x in a 0..a n, f x| ≤ ε * (a n - a 0) := by
  have hid (i : ℕ) (hi : i < n) :
      (a (i + 1) - a i) * f (tag i) - (∫ x in a i..a (i + 1), f x) =
        ∫ x in a i..a (i + 1), f (tag i) - f x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hint i hi),
      intervalIntegral.integral_const, smul_eq_mul]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals hint
  have heq :
      (∑ i ∈ range n, (a (i + 1) - a i) * f (tag i)) -
        (∫ x in a 0..a n, f x) =
      ∑ i ∈ range n, ∫ x in a i..a (i + 1), f (tag i) - f x := by
    rw [← hsplit, ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    exact hid i (mem_range.mp hi)
  rw [heq]
  calc
    _ ≤ ∑ i ∈ range n, |∫ x in a i..a (i + 1), f (tag i) - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range n, ε * (a (i + 1) - a i) := by
      apply sum_le_sum
      intro i hi
      have hin := mem_range.mp hi
      have hlocal := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun x => f (tag i) - f x) (a := a i) (b := a (i + 1)) (C := ε) (by
          intro x hx
          rw [Set.uIoc_of_le (horder i hin)] at hx
          simpa only [Real.norm_eq_abs] using hosc i hin x ⟨hx.1.le, hx.2⟩)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (horder i hin))]
        using hlocal
    _ = ε * (a n - a 0) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub]

end SpringerLean

#print axioms SpringerLean.tagged_interval_sum_error
