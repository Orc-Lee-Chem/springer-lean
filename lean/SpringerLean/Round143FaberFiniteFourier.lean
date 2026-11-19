import SpringerLean.Round142SixCombination

namespace SpringerLean

/-- Finite frequencies of an `N`th Faber boundary factor. -/
noncomputable def faberFiniteSupport (N M : ℕ) : Finset ℤ :=
  (Finset.range (M + 1)).image (fun j : ℕ => (N : ℤ) - (j : ℤ))

theorem faberFiniteSupport_injective (N M : ℕ) :
    Set.InjOn (fun j : ℕ => (N : ℤ) - (j : ℤ))
      (Finset.range (M + 1) : Set ℕ) := by
  intro i hi j hj hij
  change (N : ℤ) - (i : ℤ) = (N : ℤ) - (j : ℤ) at hij
  have : (i : ℤ) = (j : ℤ) := by omega
  exact_mod_cast this

theorem faber_fourier_mode (N j : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    fourier (N : ℤ) θ * (fourier (-1) θ) ^ j =
      fourier ((N : ℤ) - (j : ℤ)) θ := by
  rw [fourier_neg_one_pow, ← fourier_add]
  congr 1

theorem faberFiniteBoundary_eq_fourier
    (N : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    fourier (N : ℤ) θ *
      (∑ j ∈ Finset.range (M + 1), c j * (fourier (-1) θ) ^ j) =
    finiteFourierPolynomial (2 * Real.pi) (faberFiniteSupport N M)
      (fun m : ℤ => c ((N : ℤ) - m).toNat) θ := by
  classical
  rw [finiteFourierPolynomial, faberFiniteSupport,
    Finset.sum_image (faberFiniteSupport_injective N M)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : ((N : ℤ) - ((N : ℤ) - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  calc
    fourier (N : ℤ) θ * (c j * (fourier (-1) θ) ^ j) =
        c j * (fourier (N : ℤ) θ * (fourier (-1) θ) ^ j) := by ring
    _ = c j * fourier ((N : ℤ) - (j : ℤ)) θ := by
      rw [faber_fourier_mode]

theorem faberFiniteSupport_signed_sum
    (N : ℕ) (c : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ faberFiniteSupport N M,
      (m : ℝ) * ‖c ((N : ℤ) - m).toNat‖ ^ 2) =
      ∑ j ∈ Finset.range (M + 1),
        ((N : ℝ) - (j : ℝ)) * ‖c j‖ ^ 2 := by
  classical
  rw [faberFiniteSupport,
    Finset.sum_image (faberFiniteSupport_injective N M)]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoeff : ((N : ℤ) - ((N : ℤ) - (j : ℤ))).toNat = j := by omega
  rw [hcoeff]
  push_cast
  ring

/-- All later Faber orders reuse the same finite Fourier area formula. -/
theorem faberFiniteBoundary_oriented_area
    (N : ℕ) (c : ℕ → ℂ) (M : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (fourier (N : ℤ) (θ : AddCircle (2 * Real.pi)) *
        (∑ j ∈ Finset.range (M + 1),
          c j * (fourier (-1) (θ : AddCircle (2 * Real.pi))) ^ j)).re *
        deriv (fun t : ℝ =>
          (fourier (N : ℤ) (t : AddCircle (2 * Real.pi)) *
            (∑ j ∈ Finset.range (M + 1),
              c j * (fourier (-1) (t : AddCircle (2 * Real.pi))) ^ j)).im) θ) =
      Real.pi * (∑ j ∈ Finset.range (M + 1),
        ((N : ℝ) - (j : ℝ)) * ‖c j‖ ^ 2) := by
  simpa only [faberFiniteBoundary_eq_fourier,
    faberFiniteSupport_signed_sum] using
    (finiteFourierPolynomial_oriented_boundary
      (faberFiniteSupport N M)
      (fun m : ℤ => c ((N : ℤ) - m).toNat))

end SpringerLean
