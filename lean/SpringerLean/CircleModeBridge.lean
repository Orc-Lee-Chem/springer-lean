import SpringerLean.UniformDerivative

open AddCircle
open scoped ComplexConjugate

namespace SpringerLean

/-- The complex point on the circle of radius `ρ` at an additive angle. -/
noncomputable def exteriorCirclePoint (ρ : ℝ)
    (θ : AddCircle (2 * Real.pi)) : ℂ :=
  (ρ : ℂ) * fourier 1 θ

theorem exteriorCirclePoint_norm {ρ : ℝ} (hρ : 0 < ρ)
    (θ : AddCircle (2 * Real.pi)) :
    ‖exteriorCirclePoint ρ θ‖ = ρ := by
  simp [exteriorCirclePoint, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ, fourier_apply,
    Circle.norm_coe]

theorem exteriorCirclePoint_mem_exteriorDisk {ρ : ℝ} (hρ : 1 < ρ)
    (θ : AddCircle (2 * Real.pi)) :
    exteriorCirclePoint ρ θ ∈ exteriorDisk := by
  change 1 < ‖exteriorCirclePoint ρ θ‖
  rw [exteriorCirclePoint_norm (by linarith) θ]
  exact hρ

theorem exteriorCirclePoint_inv (ρ : ℝ)
    (θ : AddCircle (2 * Real.pi)) :
    (exteriorCirclePoint ρ θ)⁻¹ =
      (ρ : ℂ)⁻¹ * fourier (-1) θ := by
  unfold exteriorCirclePoint
  rw [mul_inv_rev]
  have hnorm : ‖fourier (T := 2 * Real.pi) 1 θ‖ = 1 := by
    rw [fourier_apply, Circle.norm_coe]
  rw [Complex.inv_eq_conj hnorm, ← fourier_neg]
  ring

private theorem fourier_neg_one_pow (T : ℝ) (θ : AddCircle T)
    (k : ℕ) :
    (fourier (-1) θ) ^ k = fourier (-(k : ℤ)) θ := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (fourier (-1) θ) ^ (k + 1) =
          (fourier (-1) θ) ^ k * fourier (-1) θ := pow_succ _ _
        _ = fourier (-(k : ℤ)) θ * fourier (-1) θ := by rw [ih]
        _ = fourier (-(k : ℤ) + (-1)) θ := fourier_add.symm
        _ = fourier (-(↑(k + 1) : ℤ)) θ := by
          have hidx : -(↑(k + 1) : ℤ) = -(↑k : ℤ) + (-1) := by omega
          rw [hidx]

theorem exteriorCirclePoint_inv_pow (ρ : ℝ)
    (θ : AddCircle (2 * Real.pi)) (j : ℕ) :
    ((exteriorCirclePoint ρ θ)⁻¹) ^ (j + 1) =
      ((ρ : ℂ)⁻¹) ^ (j + 1) *
        fourier (-((j : ℤ) + 1)) θ := by
  rw [exteriorCirclePoint_inv ρ θ, mul_pow,
    fourier_neg_one_pow]
  congr 1

private theorem sum_Icc_one_eq_sum_range_succ (f : ℕ → ℂ)
    (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, f j) =
      ∑ k ∈ Finset.range M, f (k + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega),
        Finset.sum_range_succ, ih]

/-- The circle polynomial is the finite Laurent derivative sum at the
actual complex point `ρ e^{iθ}`. -/
theorem exteriorDerivativePartialCircle_eq_inverse_sum
    (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    exteriorDerivativePartialCircle F ρ M θ =
      1 - ∑ j ∈ Finset.Icc 1 M,
        (j : ℂ) * exteriorForwardCoeff F j *
          ((exteriorCirclePoint ρ θ)⁻¹) ^ (j + 1) := by
  rw [exteriorDerivativePartialCircle_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [exteriorCirclePoint_inv_pow ρ θ j]
  ring

theorem exteriorDerivativePartialCircle_eq_deriv_partial
    (F : ℂ → ℂ) (ρ : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    exteriorDerivativePartialCircle F ρ M θ =
      1 - ((exteriorCirclePoint ρ θ) ^ 2)⁻¹ *
        (∑ k ∈ Finset.range M,
          (k + 1 : ℂ) * exteriorForwardCoeff F (k + 1) *
            ((exteriorCirclePoint ρ θ)⁻¹) ^ k) := by
  rw [exteriorDerivativePartialCircle_eq_inverse_sum]
  rw [sum_Icc_one_eq_sum_range_succ]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [inv_pow, pow_add]
  push_cast
  ring

end SpringerLean
