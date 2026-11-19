import SpringerLean.Round1851InterlacingTestMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Polynomial Finset

namespace SpringerLean

theorem chebyshev_test_sum_eq_grid (n : ℕ) (ψ : ℝ → ℝ) :
    ((Chebyshev.T ℝ (n : ℤ)).roots.map ψ).sum =
      ∑ i ∈ range n, ψ (chebyshevZeroGrid n i) := by
  rw [Chebyshev.roots_T_real]
  exact Finset.sum_image
    ((range n).nodup_map_iff_injOn.mp (Chebyshev.roots_T_real_nodup n))

theorem chebyshev_derivative_test_sum_eq_grid
    (n j : ℕ) (hj : j < n) (ψ : ℝ → ℝ) :
    ((((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))).roots).map ψ).sum =
      ∑ i ∈ range (n - j), ψ ((chebyshevRolleChain n j hj.le).grid j i) := by
  let C := chebyshevRolleChain n j hj.le
  have hanti : StrictAntiOn (C.grid j) (Set.Iio (n - j)) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Iio
    intro i _ hi hi1
    exact C.descending j (by omega) i (by simp at hi1; omega)
  have hinj : Set.InjOn (C.grid j) (range (n - j)) :=
    hanti.injOn.mono (by intro i hi; simpa using hi)
  rw [chebyshevRolleChain_roots n j hj]
  exact Finset.sum_image hinj

/-- Fixed derivative order changes a scaled real p-moment by at most
2*s^p*j/n.  This uses actual root multisets, with multiplicity, and all
real p>0.  There is no probability weak-convergence premise. -/
theorem chebyshev_derivative_abs_rpow_moment_discrepancy
    (n j : ℕ) (hj : j < n) (s p : ℝ) (hs : 0 ≤ s) (hp : 0 < p) :
    |(((Chebyshev.T ℝ (n : ℤ)).roots.map (fun x => |s * x| ^ p)).sum) / n -
        (((((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))).roots).map
          (fun x => |s * x| ^ p)).sum) / ((n : ℝ) - j)| ≤
      2 * s ^ p * (j : ℝ) / n := by
  let C := chebyshevRolleChain n j hj.le
  let psiPlus : ℝ → ℝ := fun x => (max (s * x) 0) ^ p
  let psiMinus : ℝ → ℝ := fun x => (max (-(s * x)) 0) ^ p
  have hplus : Monotone psiPlus := by
    intro x y hxy
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le_max (mul_le_mul_of_nonneg_left hxy hs) le_rfl) hp.le
  have hminus : Antitone psiMinus := by
    intro x y hxy
    exact Real.rpow_le_rpow (le_max_right _ _)
      (max_le_max (neg_le_neg (mul_le_mul_of_nonneg_left hxy hs)) le_rfl) hp.le
  have hplusval (i : ℕ) (_ : i < n) :
      0 ≤ psiPlus (chebyshevZeroGrid n i) ∧ psiPlus (chebyshevZeroGrid n i) ≤ s ^ p := by
    constructor
    · exact Real.rpow_nonneg (le_max_right _ _) _
    · apply Real.rpow_le_rpow (le_max_right _ _) _ hp.le
      apply max_le
      · have hc := Real.cos_le_one ((2 * (i : ℝ) + 1) * Real.pi / (2 * n))
        simpa only [chebyshevZeroGrid, mul_one] using mul_le_mul_of_nonneg_left hc hs
      · exact hs
  have hminusval (i : ℕ) (_ : i < n) :
      0 ≤ psiMinus (chebyshevZeroGrid n i) ∧ psiMinus (chebyshevZeroGrid n i) ≤ s ^ p := by
    constructor
    · exact Real.rpow_nonneg (le_max_right _ _) _
    · apply Real.rpow_le_rpow (le_max_right _ _) _ hp.le
      apply max_le
      · have hc := Real.neg_one_le_cos ((2 * (i : ℝ) + 1) * Real.pi / (2 * n))
        have hh := mul_le_mul_of_nonneg_left hc hs
        dsimp only [chebyshevZeroGrid]
        nlinarith
      · exact hs
  have hbr := C.original_brackets j le_rfl
  have h1 := interlacing_monotone_test_average_discrepancy n j hj
    (chebyshevZeroGrid n) (C.grid j) psiPlus (s ^ p) hbr (Or.inl hplus) hplusval
  have h2 := interlacing_monotone_test_average_discrepancy n j hj
    (chebyshevZeroGrid n) (C.grid j) psiMinus (s ^ p) hbr (Or.inr hminus) hminusval
  have hsplit (x : ℝ) : |s * x| ^ p = psiPlus x + psiMinus x := by
    by_cases hx : 0 ≤ s * x
    · simp only [psiPlus, psiMinus, abs_of_nonneg hx, max_eq_left hx,
        max_eq_right (neg_nonpos.mpr hx), Real.zero_rpow hp.ne', add_zero]
    · have hx' : s * x ≤ 0 := le_of_not_ge hx
      simp only [psiPlus, psiMinus, abs_of_nonpos hx', max_eq_right hx',
        max_eq_left (neg_nonneg.mpr hx'), Real.zero_rpow hp.ne', zero_add]
  rw [chebyshev_test_sum_eq_grid, chebyshev_derivative_test_sum_eq_grid n j hj]
  simp_rw [hsplit, Finset.sum_add_distrib, add_div]
  have habs := abs_add_le
    ((∑ i ∈ range n, psiPlus (chebyshevZeroGrid n i)) / n -
      (∑ i ∈ range (n - j), psiPlus (C.grid j i)) / ((n : ℝ) - j))
    ((∑ i ∈ range n, psiMinus (chebyshevZeroGrid n i)) / n -
      (∑ i ∈ range (n - j), psiMinus (C.grid j i)) / ((n : ℝ) - j))
  have heq :
      (∑ i ∈ range n, psiPlus (chebyshevZeroGrid n i)) / n +
        (∑ i ∈ range n, psiMinus (chebyshevZeroGrid n i)) / n -
        ((∑ i ∈ range (n - j), psiPlus (C.grid j i)) / ((n : ℝ) - j) +
          (∑ i ∈ range (n - j), psiMinus (C.grid j i)) / ((n : ℝ) - j)) =
      ((∑ i ∈ range n, psiPlus (chebyshevZeroGrid n i)) / n -
        (∑ i ∈ range (n - j), psiPlus (C.grid j i)) / ((n : ℝ) - j)) +
      ((∑ i ∈ range n, psiMinus (chebyshevZeroGrid n i)) / n -
        (∑ i ∈ range (n - j), psiMinus (C.grid j i)) / ((n : ℝ) - j)) := by ring
  change |(∑ i ∈ range n, psiPlus (chebyshevZeroGrid n i)) / n +
    (∑ i ∈ range n, psiMinus (chebyshevZeroGrid n i)) / n -
    ((∑ i ∈ range (n - j), psiPlus (C.grid j i)) / ((n : ℝ) - j) +
      (∑ i ∈ range (n - j), psiMinus (C.grid j i)) / ((n : ℝ) - j))| ≤ _
  rw [heq]
  exact (habs.trans (add_le_add h1 h2)).trans_eq (by ring)

end SpringerLean

#print axioms SpringerLean.chebyshev_derivative_abs_rpow_moment_discrepancy
