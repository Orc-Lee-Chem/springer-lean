import SpringerLean.Round250GeneralFaberPolynomial

namespace SpringerLean
open PowerSeries

/-- The coefficient-polynomial correction of 1 - w x + x f(x). -/
noncomputable def generalFaberGeneratorCorrection
    {A : Type*} [CommRing A] (f : PowerSeries A) :
    PowerSeries (Polynomial A) :=
  PowerSeries.C Polynomial.X * PowerSeries.X -
    PowerSeries.X * PowerSeries.map Polynomial.C f

@[simp] theorem generalFaberGeneratorCorrection_constantCoeff
    {A : Type*} [CommRing A] (f : PowerSeries A) :
    PowerSeries.constantCoeff (generalFaberGeneratorCorrection f) = 0 := by
  simp [generalFaberGeneratorCorrection]

@[simp] theorem generalFaberGeneratorCorrection_coeff_succ
    {A : Type*} [CommRing A] (f : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff (n + 1) (generalFaberGeneratorCorrection f) =
      (if n = 0 then Polynomial.X else 0) -
        Polynomial.C (PowerSeries.coeff n f) := by
  simp [generalFaberGeneratorCorrection, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_C]

/-- Uniform finite recurrence for the Faber polynomials, directly from
the formal logarithmic derivative. It is suitable for all finite orders. -/
theorem generalFaberPolynomial_antidiagonal_recurrence
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (f : PowerSeries A) (n : ℕ) :
    generalFaberPolynomial f (n + 1) =
      ((n + 1 : ℕ) : Polynomial A) *
          PowerSeries.coeff (n + 1) (generalFaberGeneratorCorrection f) +
        ∑ ij ∈ Finset.antidiagonal n,
          generalFaberPolynomial f (ij.1 + 1) *
            PowerSeries.coeff ij.2 (generalFaberGeneratorCorrection f) := by
  let T := generalFaberGeneratorCorrection f
  have hT : PowerSeries.constantCoeff T = 0 := by simp [T]
  have hB : (1 - T : PowerSeries (Polynomial A)) =
      PowerSeries.map Polynomial.C (1 + PowerSeries.X * f) -
        PowerSeries.C Polynomial.X * PowerSeries.X := by
    dsimp only [T, generalFaberGeneratorCorrection]
    simp only [map_add, map_one, map_mul, PowerSeries.map_X]
    ring
  have h := formal_negative_log_coeff_recurrence T hT n
  dsimp only at h
  rw [hB] at h
  simpa only [generalFaberPolynomial, T] using h

end SpringerLean
