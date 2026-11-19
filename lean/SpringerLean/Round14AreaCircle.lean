import SpringerLean.Round14ActualParseval
import SpringerLean.AreaFinite

open Filter MeasureTheory
open scoped Topology

namespace SpringerLean

/-- The finite area theorem bounds every finite Taylor energy on an interior circle. -/
theorem exteriorForwardCoeff_finite_circle_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (M : ℕ) :
    (∑ j ∈ Finset.range M,
      ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j)) ≤ r ^ 2 := by
  let b := exteriorForwardCoeff F
  have hterm (j : ℕ) (hj : j ∈ (Finset.range M).erase 0) :
      ‖b j‖ ^ 2 * r ^ (2 * j) ≤
        r ^ 2 * ((j : ℝ) * ‖b j‖ ^ 2) := by
    have hj1 : 1 ≤ j := by
      have hj0 := (Finset.mem_erase.mp hj).1
      omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hp : r ^ (2 * (k + 1)) = r ^ 2 * r ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
    have hpow : r ^ (2 * k) ≤ 1 := pow_le_one₀ hr0 hr1
    rw [hp]
    have htail : r ^ 2 * r ^ (2 * k) ≤ r ^ 2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hpow (sq_nonneg r)
    have hmain : ‖b (k + 1)‖ ^ 2 * (r ^ 2 * r ^ (2 * k)) ≤
        ‖b (k + 1)‖ ^ 2 * r ^ 2 :=
      mul_le_mul_of_nonneg_left htail (sq_nonneg _)
    calc
      _ ≤ ‖b (k + 1)‖ ^ 2 * r ^ 2 := hmain
      _ ≤ r ^ 2 * ((↑(k + 1) : ℝ) * ‖b (k + 1)‖ ^ 2) := by
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        have hcoef : ‖b (k + 1)‖ ^ 2 ≤
            ((↑(k + 1) : ℝ) * ‖b (k + 1)‖ ^ 2) := by
          push_cast
          nlinarith [mul_nonneg hk (sq_nonneg (‖b (k + 1)‖))]
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hcoef (sq_nonneg r)
  have hsum :
      (∑ j ∈ (Finset.range M).erase 0,
        ‖b j‖ ^ 2 * r ^ (2 * j)) ≤
        r ^ 2 * ∑ j ∈ (Finset.range M).erase 0,
          ((j : ℝ) * ‖b j‖ ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => hterm j hj)
  have hsubset : (Finset.range M).erase 0 ⊆ Finset.Icc 1 M := by
    intro j hj
    obtain ⟨hj0, hjM⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by simp only [Finset.mem_range] at hjM; omega⟩
  have harea :
      (∑ j ∈ (Finset.range M).erase 0,
        ((j : ℝ) * ‖b j‖ ^ 2)) ≤ 1 := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc 1 M, ((j : ℝ) * ‖b j‖ ^ 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro j _ _
        positivity
      _ ≤ 1 := exteriorForwardCoeff_finite_area F hc M
  calc
    (∑ j ∈ Finset.range M, ‖b j‖ ^ 2 * r ^ (2 * j)) =
        ∑ j ∈ (Finset.range M).erase 0, ‖b j‖ ^ 2 * r ^ (2 * j) := by
      exact (Finset.sum_erase (Finset.range M)
        (by simp [b, exteriorForwardCoeff_zero])).symm
    _ ≤ r ^ 2 * ∑ j ∈ (Finset.range M).erase 0,
        ((j : ℝ) * ‖b j‖ ^ 2) := hsum
    _ ≤ r ^ 2 := by nlinarith [sq_nonneg r]

/-- The actual forward correction has circle square energy at most `r²`. -/
theorem exteriorForwardGerm_circle_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage
      (fun z : ℂ => ‖exteriorForwardGerm F z‖ ^ 2) 0 r ≤ r ^ 2 := by
  exact le_of_tendsto
    (exteriorForwardGerm_circle_energy_tendsto F hc hr0 hr1)
    (Filter.Eventually.of_forall fun M =>
      exteriorForwardCoeff_finite_circle_energy_le F hc hr0.le hr1.le M)

end SpringerLean
