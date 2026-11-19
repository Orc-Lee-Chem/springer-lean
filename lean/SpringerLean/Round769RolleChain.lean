import SpringerLean.Round768RolleGridConstruction

namespace SpringerLean

open Polynomial

/-- A finite chain of ordered root grids, one grid for each derivative. -/
structure RolleGridChain (p : ℝ[X]) (n j : ℕ) (x₀ : ℕ → ℝ) where
  grid : ℕ → ℕ → ℝ
  initial : grid 0 = x₀
  roots : ∀ r ≤ j, ∀ k < n - r,
    ((derivative^[r]) p).eval (grid r k) = 0
  descending : ∀ r ≤ j, ∀ k < n - r - 1,
    grid r (k + 1) < grid r k
  interlacing : ∀ r < j, ∀ k < n - (r + 1),
    grid r (k + 1) < grid (r + 1) k ∧
      grid (r + 1) k < grid r k

/-- Rolle's theorem constructs interlacing grids at every derivative level
through any prescribed finite order. -/
noncomputable def exists_rolle_grid_chain (p : ℝ[X]) (n j : ℕ) (hj : j ≤ n)
    (x₀ : ℕ → ℝ)
    (hroot : ∀ k < n, p.eval (x₀ k) = 0)
    (hdesc : ∀ k < n - 1, x₀ (k + 1) < x₀ k) :
    RolleGridChain p n j x₀ := by
  induction j with
  | zero =>
      refine ⟨(fun _ => x₀), rfl, ?_, ?_, ?_⟩
      · intro r hr k hk
        have hr0 : r = 0 := by omega
        subst r
        simpa using hroot k hk
      · intro r hr k hk
        have hr0 : r = 0 := by omega
        subst r
        exact hdesc k hk
      · intro r hr
        omega
  | succ j ih =>
      have hjprev : j ≤ n := by omega
      let C := ih hjprev
      have hjlt : j < n := by omega
      have hlen : n - j = (n - (j + 1)) + 1 := by omega
      have hrootj : ∀ k < (n - (j + 1)) + 1,
          ((derivative^[j]) p).eval (C.grid j k) = 0 := by
        intro k hk
        exact C.roots j (by omega) k (by omega)
      have hdescj : ∀ k < n - (j + 1),
          C.grid j (k + 1) < C.grid j k := by
        intro k hk
        exact C.descending j (by omega) k (by omega)
      let hex := exists_derivative_interlacing_grid ((derivative^[j]) p)
        (n - (j + 1)) (C.grid j) hrootj hdescj
      let y := Classical.choose hex
      have hy := (Classical.choose_spec hex).1
      have hy_desc := (Classical.choose_spec hex).2
      let g : ℕ → ℕ → ℝ := fun r => if r = j + 1 then y else C.grid r
      have gold (r : ℕ) (hr : r ≤ j) : g r = C.grid r := by
        simp [g, show r ≠ j + 1 by omega]
      have gnew : g (j + 1) = y := by simp [g]
      refine ⟨g, ?_, ?_, ?_, ?_⟩
      · simpa [gold 0 (by omega)] using C.initial
      · intro r hr k hk
        by_cases hre : r = j + 1
        · subst r
          rw [gnew]
          have hk' : k < n - (j + 1) := hk
          have h := (hy k hk').1
          simpa only [Function.iterate_succ_apply'] using h
        · rw [gold r (by omega)]
          exact C.roots r (by omega) k hk
      · intro r hr k hk
        by_cases hre : r = j + 1
        · subst r
          rw [gnew]
          exact hy_desc k hk
        · rw [gold r (by omega)]
          exact C.descending r (by omega) k hk
      · intro r hr k hk
        by_cases hre : r = j
        · subst r
          rw [gold j (by omega), gnew]
          have h := hy k hk
          exact ⟨h.2.1, h.2.2⟩
        · rw [gold r (by omega), gold (r + 1) (by omega)]
          exact C.interlacing r (by omega) k (by omega)

/-- A constructed derivative-root chain inherits the `j`-step threshold
count comparison. -/
theorem RolleGridChain.count_discrepancy {p : ℝ[X]} {n j : ℕ}
    {x₀ : ℕ → ℝ} (C : RolleGridChain p n j x₀)
    (hj : j ≤ n) (t : ℝ) :
    upperGridCount (C.grid j) (n - j) t ≤ upperGridCount x₀ n t ∧
      upperGridCount x₀ n t ≤ upperGridCount (C.grid j) (n - j) t + j := by
  have hxy : ∀ r < j, ∀ k < (n - j) + j - (r + 1),
      C.grid r (k + 1) ≤ C.grid (r + 1) k ∧
        C.grid (r + 1) k ≤ C.grid r k := by
    intro r hr k hk
    have hlen : (n - j) + j = n := Nat.sub_add_cancel hj
    have h := C.interlacing r hr k (by omega)
    exact ⟨h.1.le, h.2.le⟩
  have h := upperGridCount_iterated_interlacing (n - j) j C.grid t hxy
  simpa only [Nat.sub_add_cancel hj, C.initial] using h

end SpringerLean

#print axioms SpringerLean.exists_rolle_grid_chain
#print axioms SpringerLean.RolleGridChain.count_discrepancy
