import SpringerLean.RegularEnergyLimit

open MeasureTheory
open scoped ComplexConjugate

namespace SpringerLean

/-- Exact normalized disk energy of the derivative of a finite Taylor
polynomial. The coefficient `d (j+1)` belongs to `u^(j+1)`. -/
theorem finite_derivative_modes_energy (d : ℕ → ℂ) (N : ℕ) :
    (Real.pi)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        ‖∑ j ∈ Finset.range N,
          ((j + 1 : ℂ) * d (j + 1)) * (conj z) ^ j‖ ^ 2 ∂volume) =
      ∑ j ∈ Finset.range N,
        (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2 := by
  let c : ℕ → ℂ := fun j => (j + 1 : ℂ) * d (j + 1)
  have h := finiteAntiPolynomial_energy c N
  have hterm (j : ℕ) :
      ‖c j‖ ^ 2 / (j + 1 : ℝ) =
        (j + 1 : ℝ) * ‖d (j + 1)‖ ^ 2 := by
    dsimp [c]
    rw [norm_mul]
    have hn : ‖(j + 1 : ℂ)‖ = (j + 1 : ℝ) := by norm_cast
    rw [hn]
    have hj : (j + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  simpa only [finiteAntiPolynomial, c, hterm] using h

end SpringerLean
