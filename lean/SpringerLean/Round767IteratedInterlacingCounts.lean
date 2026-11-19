import SpringerLean.Round766InterlacedZeroCounts

namespace SpringerLean

/-- A chain of `j` one-step count comparisons has discrepancy at most `j`. -/
theorem count_chain_discrepancy (c : ℕ → ℕ) (j : ℕ)
    (hstep : ∀ r < j, c (r + 1) ≤ c r ∧ c r ≤ c (r + 1) + 1) :
    c j ≤ c 0 ∧ c 0 ≤ c j + j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hprev : ∀ r < j,
          c (r + 1) ≤ c r ∧ c r ≤ c (r + 1) + 1 := by
        intro r hr
        exact hstep r (by omega)
      have h := ih hprev
      have hnext := hstep j (by omega)
      omega

/-- Threshold counts in a finite chain of interlacing arrays differ by
at most the number of steps. `x r` is the grid at derivative level `r`;
the length drops by one at each step. -/
theorem upperGridCount_iterated_interlacing
    (m j : ℕ) (x : ℕ → ℕ → ℝ) (t : ℝ)
    (hxy : ∀ r < j, ∀ k < m + j - (r + 1),
      x r (k + 1) ≤ x (r + 1) k ∧ x (r + 1) k ≤ x r k) :
    upperGridCount (x j) m t ≤ upperGridCount (x 0) (m + j) t ∧
      upperGridCount (x 0) (m + j) t ≤ upperGridCount (x j) m t + j := by
  let c : ℕ → ℕ := fun r => upperGridCount (x r) (m + j - r) t
  have hstep : ∀ r < j, c (r + 1) ≤ c r ∧ c r ≤ c (r + 1) + 1 := by
    intro r hr
    have hrle : r + 1 ≤ m + j := by omega
    have hlen : m + j - r = (m + j - (r + 1)) + 1 := by omega
    have h := upperGridCount_interlacing (m + j - (r + 1))
      (x r) (x (r + 1)) t (hxy r hr)
    simpa only [c, hlen] using h
  have h := count_chain_discrepancy c j hstep
  simpa only [c, Nat.add_sub_cancel_right, Nat.sub_zero] using h

end SpringerLean

#print axioms SpringerLean.count_chain_discrepancy
#print axioms SpringerLean.upperGridCount_iterated_interlacing
