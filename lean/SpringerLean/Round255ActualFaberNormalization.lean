import SpringerLean.Round254PolynomialReciprocal
import SpringerLean.Round251ActualFormalFaber

namespace SpringerLean
open PowerSeries

/-- All-order reciprocal Faber normalization in ordinary power series.
Every coefficient belongs to the same actual F. In particular all positive
frequencies other than the leading one vanish, uniformly in the order. -/
theorem exteriorGeneralFaberFormalFactor_normalization
    (F : ℂ → ℂ) (n : ℕ) :
    polynomialFormalReciprocalFactor
        (formalExteriorPhi (exteriorFormalForward F))
        (exteriorGeneralFaberPolynomial F (n + 1)) (n + 1) =
      1 + PowerSeries.C ((n + 1 : ℕ) : ℂ) * PowerSeries.X ^ (n + 1) *
        PowerSeries.coeff (n + 1) (exteriorFormalGrunskyKernel F) := by
  let h := HahnSeries.ofPowerSeries ℤ ℂ
  let φ := formalExteriorPhi (exteriorFormalForward F)
  let P := exteriorGeneralFaberPolynomial F (n + 1)
  have hy : h PowerSeries.X ≠ 0 := by
    intro hz
    have hx : (PowerSeries.X : PowerSeries ℂ) = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
        (by simpa [h] using hz)
    exact PowerSeries.X_ne_zero hx
  have hP : P.natDegree ≤ n + 1 :=
    generalFaberPolynomial_natDegree_le (exteriorFormalForward F) (n + 1)
  have hmap := polynomialFormalReciprocalFactor_map φ P (n + 1) hP h hy
  have heval : P.eval₂ (h.comp PowerSeries.C)
      ((h PowerSeries.X)⁻¹ * h φ) =
      ((h PowerSeries.X)⁻¹) ^ (n + 1) +
        ((n + 1 : ℕ) : LaurentSeries ℂ) *
          h (PowerSeries.coeff (n + 1) (exteriorFormalGrunskyKernel F)) := by
    simpa [P, φ, h, exteriorFormalLaurent] using
      exteriorGeneralFaberPolynomial_formalLaurent_eval F n
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  change h (polynomialFormalReciprocalFactor φ P (n + 1)) = _
  rw [hmap, heval]
  have hcancel : (h PowerSeries.X) ^ (n + 1) *
      ((h PowerSeries.X)⁻¹) ^ (n + 1) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hy, one_pow]
  have hcast : h (PowerSeries.C ((n + 1 : ℕ) : ℂ)) =
      ((n + 1 : ℕ) : LaurentSeries ℂ) := by
    simp [h]
  simp only [map_add, map_one, map_mul, map_pow]
  rw [hcast, mul_add, hcancel]
  ring

end SpringerLean
