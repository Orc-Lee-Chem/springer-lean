import SpringerLean.Round57EqualityPrelude
import SpringerLean.Round14AreaCircle

open MeasureTheory Filter

namespace SpringerLean

private theorem forward_finite_circle_energy_quantitative
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (M : ℕ) (hM : 2 ≤ M) :
    (∑ j ∈ Finset.range M,
      ‖exteriorForwardCoeff F j‖ ^ 2 * r ^ (2 * j)) ≤
    r ^ 2 * ‖exteriorForwardCoeff F 1‖ ^ 2 +
      r ^ 4 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let b := exteriorForwardCoeff F
  let t : ℕ → ℝ := fun j => ‖b j‖ ^ 2 * r ^ (2 * j)
  let w : ℕ → ℝ := fun j => (j : ℝ) * ‖b j‖ ^ 2
  have htail (j : ℕ) (hj : j ∈ Finset.Ico 2 M) :
      t j ≤ r ^ 4 * w j := by
    have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj2
    subst j
    have hpow : r ^ (2 * (2 + k)) = r ^ 4 * r ^ (2 * k) := by
      rw [show 2 * (2 + k) = 4 + 2 * k by omega, pow_add]
    have hpow1 : r ^ (2 * k) ≤ 1 := pow_le_one₀ hr0 hr1
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hcoef : ‖b (2 + k)‖ ^ 2 ≤ ((2 + k : ℕ) : ℝ) * ‖b (2 + k)‖ ^ 2 := by
      push_cast
      nlinarith [mul_nonneg hk0 (sq_nonneg (‖b (2 + k)‖))]
    dsimp [t, w]
    rw [hpow]
    calc
      ‖b (2 + k)‖ ^ 2 * (r ^ 4 * r ^ (2 * k)) ≤
          ‖b (2 + k)‖ ^ 2 * r ^ 4 := by
            exact mul_le_mul_of_nonneg_left (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow1 (pow_nonneg hr0 4) : r ^ 4 * r ^ (2 * k) ≤ r ^ 4) (sq_nonneg _)
      _ ≤ r ^ 4 * (((2 + k : ℕ) : ℝ) * ‖b (2 + k)‖ ^ 2) := by
          nlinarith [mul_nonneg (pow_nonneg hr0 4)
            (sub_nonneg.mpr hcoef)]
  have htailSum :
      (∑ j ∈ Finset.Ico 2 M, t j) ≤
        r ^ 4 * ∑ j ∈ Finset.Ico 2 M, w j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum htail
  have hsubset : insert 1 (Finset.Ico 2 M) ⊆ Finset.Icc 1 M := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Finset.mem_Icc.mpr ⟨by norm_num, (by omega)⟩
    · have hh := Finset.mem_Ico.mp hj
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hnot : 1 ∉ Finset.Ico 2 M := by simp
  have hweighted : w 1 + ∑ j ∈ Finset.Ico 2 M, w j ≤ 1 := by
    have hs :
        (∑ j ∈ insert 1 (Finset.Ico 2 M), w j) ≤
        ∑ j ∈ Finset.Icc 1 M, w j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro j _ _
      dsimp [w]
      positivity
    rw [Finset.sum_insert hnot] at hs
    exact hs.trans (exteriorForwardCoeff_finite_area F hc M)
  have hsplit :
      (∑ j ∈ Finset.range M, t j) = t 1 + ∑ j ∈ Finset.Ico 2 M, t j := by
    have hh := Finset.sum_range_add_sum_Ico t hM
    have ht0 : t 0 = 0 := by simp [t, b, exteriorForwardCoeff_zero]
    simpa [Finset.sum_range_succ, ht0] using hh.symm
  rw [hsplit]
  have ht1 : t 1 = r ^ 2 * ‖b 1‖ ^ 2 := by simp [t, mul_comm]
  rw [ht1]
  have hw1 : w 1 = ‖b 1‖ ^ 2 := by simp [w]
  rw [hw1] at hweighted
  calc
    r ^ 2 * ‖b 1‖ ^ 2 + ∑ j ∈ Finset.Ico 2 M, t j ≤
      r ^ 2 * ‖b 1‖ ^ 2 + r ^ 4 * ∑ j ∈ Finset.Ico 2 M, w j :=
        by simpa only [add_comm] using add_le_add_left htailSum (r ^ 2 * ‖b 1‖ ^ 2)
    _ ≤ r ^ 2 * ‖b 1‖ ^ 2 + r ^ 4 * (1 - ‖b 1‖ ^ 2) := by
      nlinarith [mul_nonneg (pow_nonneg hr0 4)
        (sub_nonneg.mpr (by linarith : ∑ j ∈ Finset.Ico 2 M, w j ≤
          1 - ‖b 1‖ ^ 2))]

/-- The actual forward correction has a quantitative circle deficit
controlled by the first coefficient. -/
theorem exteriorForwardGerm_circle_energy_le_firstCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun z : ℂ => ‖exteriorForwardGerm F z‖ ^ 2) 0 r ≤
      r ^ 2 * ‖exteriorForwardCoeff F 1‖ ^ 2 +
        r ^ 4 * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  exact le_of_tendsto
    (exteriorForwardGerm_circle_energy_tendsto F hc hr0 hr1)
    ((eventually_ge_atTop (2 : ℕ)).mono
      (fun M hM => forward_finite_circle_energy_quantitative F hc
        hr0.le hr1.le M hM))

end SpringerLean