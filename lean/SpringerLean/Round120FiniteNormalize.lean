import SpringerLean.Round103NormalizeFour

namespace SpringerLean

/-- The weighted Faber area estimate implies the square-root-normalized
Grunsky matrix contraction in any finite dimension. This algebraic bridge
does not depend on the exterior map or the choice of kernel. -/
theorem finiteDim_weighted_kernel_normalize
    (N : ℕ) (c : Fin N → Fin N → ℂ)
    (hweighted : ∀ α : Fin N → ℂ,
      (∑ j : Fin N, ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin N, α i * ((i.val + 1 : ℕ) : ℂ) * c j i‖ ^ 2) ≤
        ∑ i : Fin N, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2)
    (v : Fin N → ℂ) :
    (∑ j : Fin N,
      ‖∑ i : Fin N,
        ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          c j i * v i‖ ^ 2) ≤
      ∑ i : Fin N, ‖v i‖ ^ 2 := by
  let w (i : Fin N) : ℝ := ((i.val + 1 : ℕ) : ℝ)
  let s (i : Fin N) : ℂ := (Real.sqrt (w i) : ℂ)
  have hwpos (i : Fin N) : 0 < w i := by
    dsimp [w]
    positivity
  have hsne (i : Fin N) : s i ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (hwpos i))
  have hsq (i : Fin N) : s i ^ 2 = (w i : ℂ) := by
    dsimp [s]
    exact_mod_cast (Real.sq_sqrt (le_of_lt (hwpos i)))
  have hnormsq (i : Fin N) : ‖s i‖ ^ 2 = w i := by
    rw [show s i = (Real.sqrt (w i) : ℂ) by rfl,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (le_of_lt (hwpos i))]
  let α : Fin N → ℂ := fun i => (s i)⁻¹ * v i
  have hterm (i j : Fin N) :
      s j * (α i * (w i : ℂ) * c j i) =
        s j * s i * c j i * v i := by
    dsimp [α]
    rw [← hsq i]
    field_simp [hsne i]
  have hrow (j : Fin N) :
      (∑ i : Fin N, s j * s i * c j i * v i) =
        s j * (∑ i : Fin N, α i * (w i : ℂ) * c j i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (hterm i j).symm)
  have hleft :
      (∑ j : Fin N, ‖∑ i : Fin N, s j * s i * c j i * v i‖ ^ 2) =
        ∑ j : Fin N, w j *
          ‖∑ i : Fin N, α i * (w i : ℂ) * c j i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrow, norm_mul, mul_pow, hnormsq]
  have hright :
      (∑ i : Fin N, w i * ‖α i‖ ^ 2) =
        ∑ i : Fin N, ‖v i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [α]
    rw [norm_mul, norm_inv, mul_pow, ← hnormsq i]
    have hn : ‖s i‖ ≠ 0 := norm_ne_zero_iff.mpr (hsne i)
    field_simp
  change (∑ j : Fin N, ‖∑ i : Fin N, s j * s i * c j i * v i‖ ^ 2) ≤
    ∑ i : Fin N, ‖v i‖ ^ 2
  rw [hleft, ← hright]
  exact hweighted α

end SpringerLean
