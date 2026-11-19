import SpringerLean.Round1621EnergyRampOnCell

namespace SpringerLean

/-- Generic finite telescoping formula for a piecewise ramp sum. This
avoids expanding the 21-cell spline separately on every cell. -/
theorem sum_range_piecewise_telescopes
    (f : ℕ → ℝ) (j n : ℕ) (c : ℝ) (hjn : j < n) :
    (∑ i ∈ Finset.range n,
      if i < j then f (i+1)-f i else if i = j then c else 0) =
        f j-f 0+c := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hjn' : j < n
    · have hnot : ¬ n < j := by omega
      have hne : n ≠ j := by omega
      rw [ih hjn']
      simp [hnot, hne]
    · have hjeq : j = n := by omega
      subst j
      have hprefix :
          (∑ i ∈ Finset.range n,
            if i < n then f (i+1)-f i else if i = n then c else 0) =
            ∑ i ∈ Finset.range n, (f (i+1)-f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.mem_range.mp hi]
      rw [hprefix, Finset.sum_range_sub]
      simp

end SpringerLean

#print axioms SpringerLean.sum_range_piecewise_telescopes
