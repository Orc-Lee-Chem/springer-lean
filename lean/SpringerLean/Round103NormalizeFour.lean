import SpringerLean.Round102ThirdMode

namespace SpringerLean

/-- Normalize a weighted four-dimensional complex matrix contraction by
the square roots of its positive integer mode weights. -/
theorem finiteFour_weighted_kernel_normalize
    (c : Fin 4 → Fin 4 → ℂ)
    (hweighted : ∀ α : Fin 4 → ℂ,
      (∑ j : Fin 4, ((j.val + 1 : ℕ) : ℝ) *
        ‖∑ i : Fin 4, α i * ((i.val + 1 : ℕ) : ℂ) * c j i‖ ^ 2) ≤
        ∑ i : Fin 4, ((i.val + 1 : ℕ) : ℝ) * ‖α i‖ ^ 2)
    (v : Fin 4 → ℂ) :
    (∑ j : Fin 4,
      ‖∑ i : Fin 4,
        ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          c j i * v i‖ ^ 2) ≤
      ∑ i : Fin 4, ‖v i‖ ^ 2 := by
  let w (i : Fin 4) : ℝ := ((i.val + 1 : ℕ) : ℝ)
  let s (i : Fin 4) : ℂ := (Real.sqrt (w i) : ℂ)
  have hwpos (i : Fin 4) : 0 < w i := by
    dsimp [w]
    positivity
  have hsne (i : Fin 4) : s i ≠ 0 := by
    dsimp [s]
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (hwpos i))
  have hsq (i : Fin 4) : s i ^ 2 = (w i : ℂ) := by
    dsimp [s]
    exact_mod_cast (Real.sq_sqrt (le_of_lt (hwpos i)))
  have hnormsq (i : Fin 4) : ‖s i‖ ^ 2 = w i := by
    rw [show s i = (Real.sqrt (w i) : ℂ) by rfl,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (le_of_lt (hwpos i))]
  let α : Fin 4 → ℂ := fun i => (s i)⁻¹ * v i
  have hterm (i j : Fin 4) :
      s j * (α i * (w i : ℂ) * c j i) =
        s j * s i * c j i * v i := by
    dsimp [α]
    rw [← hsq i]
    field_simp [hsne i]
  have hrow (j : Fin 4) :
      (∑ i : Fin 4, s j * s i * c j i * v i) =
        s j * (∑ i : Fin 4, α i * (w i : ℂ) * c j i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (hterm i j).symm)
  have hleft :
      (∑ j : Fin 4, ‖∑ i : Fin 4, s j * s i * c j i * v i‖ ^ 2) =
      ∑ j : Fin 4, w j * ‖∑ i : Fin 4, α i * (w i : ℂ) * c j i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hrow, norm_mul, mul_pow, hnormsq]
  have hright :
      (∑ i : Fin 4, w i * ‖α i‖ ^ 2) =
      ∑ i : Fin 4, ‖v i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [α]
    rw [norm_mul, norm_inv, mul_pow, ← hnormsq i]
    have hn : ‖s i‖ ≠ 0 := norm_ne_zero_iff.mpr (hsne i)
    field_simp
  change (∑ j : Fin 4, ‖∑ i : Fin 4, s j * s i * c j i * v i‖ ^ 2) ≤
    ∑ i : Fin 4, ‖v i‖ ^ 2
  rw [hleft, ← hright]
  exact hweighted α

/-- Square-root-normalized four-by-four Grunsky contraction for every
actual centered exterior-univalent map, with no extra matrix assumption. -/
theorem exterior_schoberKernelQ4_normalized_contraction
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : Fin 4 → ℂ) :
    (∑ j : Fin 4,
      ‖∑ i : Fin 4,
        ((Real.sqrt ((j.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt ((i.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          schoberBiCoeff (j.val + 1) (i.val + 1)
            (schoberKernelQ4
              (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
              (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
              (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
              (exteriorForwardCoeff F 7)) * v i‖ ^ 2) ≤
      ∑ i : Fin 4, ‖v i‖ ^ 2 := by
  exact finiteFour_weighted_kernel_normalize
    (fun j i => schoberBiCoeff (j.val + 1) (i.val + 1)
      (schoberKernelQ4
        (exteriorForwardCoeff F 1) (exteriorForwardCoeff F 2)
        (exteriorForwardCoeff F 3) (exteriorForwardCoeff F 4)
        (exteriorForwardCoeff F 5) (exteriorForwardCoeff F 6)
        (exteriorForwardCoeff F 7)))
    (exterior_schoberKernelQ4_weighted_contraction F hc) v

end SpringerLean
