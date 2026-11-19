import SpringerLean.Round1850RolleMomentPrelude

open Finset

namespace SpringerLean

/-- Finite interlacing controls any bounded monotone test.  This is a
direct summation alternative to a layer-cake argument, with the same
sharp normalization j/n. -/
theorem interlacing_monotone_test_average_discrepancy
    (n j : ℕ) (hj : j < n) (a b : ℕ → ℝ) (ψ : ℝ → ℝ) (C : ℝ)
    (hbracket : ∀ i < n - j, a (i + j) ≤ b i ∧ b i ≤ a i)
    (hψ : Monotone ψ ∨ Antitone ψ)
    (hvalue : ∀ i < n, 0 ≤ ψ (a i) ∧ ψ (a i) ≤ C) :
    |(∑ i ∈ range n, ψ (a i)) / n -
        (∑ i ∈ range (n - j), ψ (b i)) / ((n : ℝ) - j)| ≤
      (j : ℝ) * C / n := by
  let A := ∑ i ∈ range n, ψ (a i)
  let B := ∑ i ∈ range (n - j), ψ (b i)
  let L := ∑ i ∈ range (n - j), ψ (a i)
  let R := ∑ i ∈ range (n - j), ψ (a (i + j))
  have hcast : ((n - j : ℕ) : ℝ) = (n : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hpoint (i : ℕ) (hi : i < n - j) : 0 ≤ ψ (b i) ∧ ψ (b i) ≤ C := by
    rcases hψ with hmono | hanti
    · exact ⟨(hvalue (i + j) (by omega)).1.trans (hmono (hbracket i hi).1),
        (hmono (hbracket i hi).2).trans (hvalue i (by omega)).2⟩
    · exact ⟨(hvalue i (by omega)).1.trans (hanti (hbracket i hi).2),
        (hanti (hbracket i hi).1).trans (hvalue (i + j) (by omega)).2⟩
  have hB0 : 0 ≤ B := by
    exact sum_nonneg (fun i hi => (hpoint i (mem_range.mp hi)).1)
  have hBC : B ≤ ((n : ℝ) - j) * C := by
    calc
      B ≤ ∑ _i ∈ range (n - j), C :=
        sum_le_sum (fun i hi => (hpoint i (mem_range.mp hi)).2)
      _ = ((n : ℝ) - j) * C := by simp [hcast]
  have hsplitL : A = L + ∑ i ∈ range j, ψ (a ((n - j) + i)) := by
    have heq := sum_range_add (fun i => ψ (a i)) (n - j) j
    simpa only [Nat.sub_add_cancel hj.le, A, L] using heq
  have hsplitR : A = (∑ i ∈ range j, ψ (a i)) + R := by
    have heq := sum_range_add (fun i => ψ (a i)) j (n - j)
    simpa only [show j + (n - j) = n by omega, Nat.add_comm j, A, R] using heq
  have htail : 0 ≤ ∑ i ∈ range j, ψ (a ((n - j) + i)) := by
    apply sum_nonneg
    intro i hi
    exact (hvalue _ (by have := mem_range.mp hi; omega)).1
  have hhead : 0 ≤ ∑ i ∈ range j, ψ (a i) := by
    apply sum_nonneg
    intro i hi
    exact (hvalue _ (by have := mem_range.mp hi; omega)).1
  have htailC : (∑ i ∈ range j, ψ (a ((n - j) + i))) ≤ (j : ℝ) * C := by
    calc
      _ ≤ ∑ _i ∈ range j, C := by
        apply sum_le_sum
        intro i hi
        exact (hvalue _ (by have := mem_range.mp hi; omega)).2
      _ = _ := by simp
  have hheadC : (∑ i ∈ range j, ψ (a i)) ≤ (j : ℝ) * C := by
    calc
      _ ≤ ∑ _i ∈ range j, C := by
        apply sum_le_sum
        intro i hi
        exact (hvalue _ (by have := mem_range.mp hi; omega)).2
      _ = _ := by simp
  have hbetween : (R ≤ B ∧ B ≤ L) ∨ (L ≤ B ∧ B ≤ R) := by
    rcases hψ with hmono | hanti
    · left
      constructor <;> apply sum_le_sum <;> intro i hi
      · exact hmono (hbracket i (mem_range.mp hi)).1
      · exact hmono (hbracket i (mem_range.mp hi)).2
    · right
      constructor <;> apply sum_le_sum <;> intro i hi
      · exact hanti (hbracket i (mem_range.mp hi)).2
      · exact hanti (hbracket i (mem_range.mp hi)).1
  have hBA : B ≤ A := by rcases hbetween with h | h <;> linarith
  have hAB : A ≤ B + (j : ℝ) * C := by rcases hbetween with h | h <;> linarith
  exact normalized_real_sum_discrepancy n j hj A B C hB0 hBC hBA hAB

end SpringerLean

#print axioms SpringerLean.interlacing_monotone_test_average_discrepancy
