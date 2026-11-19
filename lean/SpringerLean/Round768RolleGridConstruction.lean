import SpringerLean.Round767IteratedInterlacingCounts

namespace SpringerLean

open Polynomial

/-- Given `m+1` strictly descending real roots of a polynomial, choose
`m` strictly descending roots of its derivative, one in each gap. -/
theorem exists_derivative_interlacing_grid (p : ℝ[X]) (m : ℕ)
    (x : ℕ → ℝ)
    (hroot : ∀ k < m + 1, p.eval (x k) = 0)
    (hdesc : ∀ k < m, x (k + 1) < x k) :
    ∃ y : ℕ → ℝ,
      (∀ k < m,
        (derivative p).eval (y k) = 0 ∧
        x (k + 1) < y k ∧ y k < x k) ∧
      (∀ k < m - 1, y (k + 1) < y k) := by
  have hgap (k : ℕ) (hk : k < m) :
      ∃ z : ℝ, x (k + 1) < z ∧ z < x k ∧ (derivative p).eval z = 0 := by
    have hleft := hroot (k + 1) (by omega)
    have hright := hroot k (by omega)
    simpa using
      polynomial_iterated_derivative_zero_between p 0 (hdesc k hk) hleft hright
  let y : ℕ → ℝ := fun k => if hk : k < m then Classical.choose (hgap k hk) else 0
  have hy (k : ℕ) (hk : k < m) :
      (derivative p).eval (y k) = 0 ∧
      x (k + 1) < y k ∧ y k < x k := by
    have hz := Classical.choose_spec (hgap k hk)
    simpa [y, hk] using ⟨hz.2.2, hz.1, hz.2.1⟩
  refine ⟨y, hy, ?_⟩
  intro k hk
  have hk0 : k < m := by omega
  have hk1 : k + 1 < m := by omega
  have h0 := hy k hk0
  have h1 := hy (k + 1) hk1
  exact lt_trans h1.2.2 h0.2.1

end SpringerLean

#print axioms SpringerLean.exists_derivative_interlacing_grid
