import SpringerLean.Round253FaberDegree
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace SpringerLean
open PowerSeries

/-- The reciprocal factor is a finite sum whenever deg P <= n. -/
noncomputable def polynomialFormalReciprocalFactor
    {A : Type*} [CommRing A]
    (φ : PowerSeries A) (P : Polynomial A) (n : ℕ) : PowerSeries A :=
  ∑ j ∈ Finset.range (n + 1),
    PowerSeries.C (P.coeff j) * PowerSeries.X ^ (n - j) * φ ^ j

/-- Exact interpretation of the finite reciprocal factor after making
the reciprocal variable invertible. -/
theorem polynomialFormalReciprocalFactor_map
    {A B : Type*} [CommRing A] [Field B]
    (φ : PowerSeries A) (P : Polynomial A) (n : ℕ)
    (hP : P.natDegree ≤ n)
    (h : PowerSeries A →+* B) (hy : h PowerSeries.X ≠ 0) :
    h (polynomialFormalReciprocalFactor φ P n) =
      (h PowerSeries.X) ^ n *
        P.eval₂ (h.comp PowerSeries.C) ((h PowerSeries.X)⁻¹ * h φ) := by
  rw [polynomialFormalReciprocalFactor, map_sum,
    Polynomial.eval₂_eq_sum_range' (n := n + 1) _ (by omega), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  simp only [map_mul, map_pow, RingHom.comp_apply]
  rw [pow_sub₀ (h PowerSeries.X) hy hjn, mul_pow, inv_pow]
  ring

end SpringerLean
