import SpringerLean.Round771ChebyshevDerivativeRoots

namespace SpringerLean

open Polynomial

/-- Number of real polynomial roots at or above a threshold, counted with
multiplicity. -/
noncomputable def upperRealRootCount (p : ℝ[X]) (t : ℝ) : ℕ :=
  (p.roots.filter (fun z => t ≤ z)).card

theorem chebyshev_derivative_upperRootCount_eq_grid (n j : ℕ)
    (hj : j < n) (t : ℝ) :
    upperRealRootCount ((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))) t =
      upperGridCount ((chebyshevRolleChain n j hj.le).grid j) (n - j) t := by
  let C := chebyshevRolleChain n j hj.le
  have hanti : StrictAntiOn (C.grid j) (Set.Iio (n - j)) := by
    apply strictAntiOn_of_succ_lt Set.ordConnected_Iio
    intro k _ hk hk1
    exact C.descending j (by omega) k (by simp at hk1; omega)
  have hinj : Set.InjOn (C.grid j) (Finset.range (n - j)) := by
    apply hanti.injOn.mono
    intro k hk
    simpa using hk
  rw [upperRealRootCount, chebyshevRolleChain_roots n j hj]
  exact upperGridCount_eq_image_filter_card (n - j) (C.grid j) t hinj

theorem chebyshev_upperRootCount_eq_grid (n : ℕ) (t : ℝ) :
    upperRealRootCount (Chebyshev.T ℝ (n : ℤ)) t =
      upperGridCount (chebyshevZeroGrid n) n t := by
  have hgrid : chebyshevZeroGrid n =
      (fun k : ℕ => Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * n))) := by
    funext k
    simp [chebyshevZeroGrid]
  have hinj : Set.InjOn (chebyshevZeroGrid n) (Finset.range n) := by
    rw [hgrid]
    exact (Finset.range n).nodup_map_iff_injOn.mp
      (Chebyshev.roots_T_real_nodup n)
  rw [upperRealRootCount, Chebyshev.roots_T_real]
  rw [hgrid]
  exact upperGridCount_eq_image_filter_card n _ t (by simpa only [hgrid] using hinj)

/-- The number of actual real zeros of the `j`th derivative of `T_n` above
any threshold differs from the number of `T_n` zeros by at most `j`.
Multiplicity is included through `Polynomial.roots`. -/
theorem chebyshev_derivative_zero_count_discrepancy (n j : ℕ)
    (hj : j < n) (t : ℝ) :
    upperRealRootCount ((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))) t ≤
        upperRealRootCount (Chebyshev.T ℝ (n : ℤ)) t ∧
      upperRealRootCount (Chebyshev.T ℝ (n : ℤ)) t ≤
        upperRealRootCount ((derivative^[j]) (Chebyshev.T ℝ (n : ℤ))) t + j := by
  have h := chebyshevRolleChain_count n j hj.le t
  rw [← chebyshev_derivative_upperRootCount_eq_grid n j hj t,
    ← chebyshev_upperRootCount_eq_grid n t] at h
  exact h

end SpringerLean

#print axioms SpringerLean.chebyshev_derivative_zero_count_discrepancy
