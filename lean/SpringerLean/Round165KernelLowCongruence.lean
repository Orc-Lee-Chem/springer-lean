import SpringerLean.Round164KernelSixDiagonalPrelude

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Low rectangular coefficient agreement for bivariate formal series. -/
def schoberLowEq (n : ℕ)
    (A B : PowerSeries (PowerSeries ℂ)) : Prop :=
  ∀ i j : ℕ, i < n → j < n →
    schoberBiCoeff i j A = schoberBiCoeff i j B

theorem schoberBiCoeff_mul_antidiagonal
    (A B : PowerSeries (PowerSeries ℂ)) (i j : ℕ) :
    schoberBiCoeff i j (A * B) =
      ∑ pq ∈ Finset.antidiagonal j,
        ∑ rs ∈ Finset.antidiagonal i,
          schoberBiCoeff rs.1 pq.1 A *
            schoberBiCoeff rs.2 pq.2 B := by
  unfold schoberBiCoeff
  rw [PowerSeries.coeff_mul]
  simp only [map_sum, PowerSeries.coeff_mul, map_mul]

theorem schoberLowEq_mul
    {n : ℕ} {A B C D : PowerSeries (PowerSeries ℂ)}
    (hAC : schoberLowEq n A C) (hBD : schoberLowEq n B D) :
    schoberLowEq n (A * B) (C * D) := by
  intro i j hi hj
  rw [schoberBiCoeff_mul_antidiagonal,
    schoberBiCoeff_mul_antidiagonal]
  apply Finset.sum_congr rfl
  intro pq hpq
  have hpqsum := (Finset.mem_antidiagonal.mp hpq)
  apply Finset.sum_congr rfl
  intro rs hrs
  have hrssum := (Finset.mem_antidiagonal.mp hrs)
  rw [hAC rs.1 pq.1 (by omega) (by omega),
    hBD rs.2 pq.2 (by omega) (by omega)]

theorem schoberLowEq_pow
    {n : ℕ} {A B : PowerSeries (PowerSeries ℂ)}
    (hAB : schoberLowEq n A B) (k : ℕ) :
    schoberLowEq n (A ^ k) (B ^ k) := by
  induction k with
  | zero => exact fun _ _ _ _ => rfl
  | succ k ih =>
      simpa only [pow_succ] using schoberLowEq_mul ih hAB

end SpringerLean
