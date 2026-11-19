import SpringerLean.Round1331FiniteExteriorParseval
import SpringerLean.Round14ActualParseval
import SpringerLean.CircleModeBridge

open AddCircle

namespace SpringerLean

private theorem fourier_neg_one_pow_actual (T : ℝ)
    (θ : AddCircle T) (j : ℕ) :
    (fourier (-1) θ) ^ j = fourier (-(j : ℤ)) θ := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        (fourier (-1) θ) ^ (j + 1) =
            (fourier (-1) θ) ^ j * fourier (-1) θ := pow_succ _ _
        _ = fourier (-(j : ℤ)) θ * fourier (-1) θ := by rw [ih]
        _ = fourier (-(j : ℤ) + (-1)) θ := fourier_add.symm
        _ = fourier (-(↑(j + 1) : ℤ)) θ := by
          have hidx : -(↑(j + 1) : ℤ) = -(↑j : ℤ) + (-1) := by omega
          rw [hidx]

/-- The negative Fourier mode in the finite exterior Parseval formula is
exactly a power of the actual reciprocal exterior-circle point. -/
theorem exteriorCirclePoint_inv_pow_all
    (r : ℝ) (θ : AddCircle (2 * Real.pi)) (j : ℕ) :
    ((exteriorCirclePoint r⁻¹ θ)⁻¹) ^ j =
      (r : ℂ) ^ j * fourier (-(j : ℤ)) θ := by
  rw [exteriorCirclePoint_inv, mul_pow]
  have hcast : ((r⁻¹ : ℝ) : ℂ)⁻¹ = (r : ℂ) := by
    push_cast
    simp
  rw [hcast, fourier_neg_one_pow_actual]

/-- The finite Fourier family is the actual leading exterior mode plus
the first `M` Taylor coefficients of the original map's forward germ,
evaluated at the reciprocal exterior-circle point. -/
theorem finiteExteriorFourierPartial_actual_eq
    (F : ℂ → ℂ) (r : ℝ) (M : ℕ)
    (θ : AddCircle (2 * Real.pi)) :
    finiteExteriorFourierPartial (exteriorForwardCoeff F) r M θ =
      exteriorCirclePoint r⁻¹ θ +
        ∑ j ∈ Finset.range M, exteriorForwardCoeff F j *
          ((exteriorCirclePoint r⁻¹ θ)⁻¹) ^ j := by
  calc
    _ = (r⁻¹ : ℂ) * fourier 1 θ +
        ∑ j ∈ Finset.range M,
          (exteriorForwardCoeff F j * (r : ℂ) ^ j) *
            fourier (-(j : ℤ)) θ :=
        finiteExteriorFourierPartial_eq _ _ _ _
    _ = exteriorCirclePoint r⁻¹ θ +
        ∑ j ∈ Finset.range M, exteriorForwardCoeff F j *
          ((exteriorCirclePoint r⁻¹ θ)⁻¹) ^ j := by
      have hlead : (r⁻¹ : ℂ) * fourier 1 θ =
          exteriorCirclePoint r⁻¹ θ := by
        simp [exteriorCirclePoint]
      rw [hlead]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [exteriorCirclePoint_inv_pow_all r θ j]
      ring

end SpringerLean

#print axioms SpringerLean.finiteExteriorFourierPartial_actual_eq
