import SpringerLean.Round769RolleChain

namespace SpringerLean

open Polynomial

noncomputable def chebyshevZeroGrid (n : ℕ) (k : ℕ) : ℝ :=
  Real.cos ((2 * k + 1) * Real.pi / (2 * n))

theorem chebyshevZeroGrid_isRoot (n k : ℕ) (hk : k < n) :
    (Chebyshev.T ℝ (n : ℤ)).eval (chebyshevZeroGrid n k) = 0 := by
  have hm : chebyshevZeroGrid n k ∈ (Chebyshev.T ℝ (n : ℤ)).roots := by
    rw [Chebyshev.roots_T_real, Finset.mem_val]
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  exact (mem_roots (Chebyshev.T_ne_zero ℝ (n : ℤ))).mp hm

theorem chebyshevZeroGrid_descending (n k : ℕ) (hk : k < n - 1) :
    chebyshevZeroGrid n (k + 1) < chebyshevZeroGrid n k := by
  have hn : 0 < n := by omega
  have hkn : k + 2 ≤ n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < 2 * n := by positivity
  have hnum : (2 * ((k + 1 : ℕ) : ℝ) + 1) ≤ 2 * n := by
    exact_mod_cast (by omega : 2 * (k + 1) + 1 ≤ 2 * n)
  have hhigh : (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) ≤
      Real.pi := by
    calc
      _ ≤ (2 * n) * Real.pi / (2 * n) := by gcongr
      _ = Real.pi := by field_simp
  have hlow : 0 ≤ (2 * (k : ℝ) + 1) * Real.pi / (2 * n) := by positivity
  have hangle : (2 * (k : ℝ) + 1) * Real.pi / (2 * n) <
      (2 * ((k + 1 : ℕ) : ℝ) + 1) * Real.pi / (2 * n) := by
    gcongr
    omega
  exact Real.cos_lt_cos_of_nonneg_of_le_pi hlow hhigh hangle

/-- A complete finite Rolle chain for the Chebyshev zero grid. -/
noncomputable def chebyshevRolleChain (n j : ℕ) (hj : j ≤ n) :
    RolleGridChain (Chebyshev.T ℝ (n : ℤ)) n j (chebyshevZeroGrid n) :=
  exists_rolle_grid_chain _ n j hj _
    (chebyshevZeroGrid_isRoot n)
    (chebyshevZeroGrid_descending n)

/-- For every derivative order, the chosen Chebyshev zero grid has threshold
counts within `j` of the original Chebyshev grid. -/
theorem chebyshevRolleChain_count (n j : ℕ) (hj : j ≤ n) (t : ℝ) :
    upperGridCount ((chebyshevRolleChain n j hj).grid j) (n - j) t ≤
        upperGridCount (chebyshevZeroGrid n) n t ∧
      upperGridCount (chebyshevZeroGrid n) n t ≤
        upperGridCount ((chebyshevRolleChain n j hj).grid j) (n - j) t + j :=
  (chebyshevRolleChain n j hj).count_discrepancy hj t

end SpringerLean

#print axioms SpringerLean.chebyshevRolleChain_count
