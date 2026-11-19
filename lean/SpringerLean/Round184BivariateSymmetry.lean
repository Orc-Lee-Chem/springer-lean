import SpringerLean.Round183SixFaberFourthMode

set_option maxHeartbeats 1000000

namespace SpringerLean

open PowerSeries

/-- Symmetry of a bivariate formal series on a finite coefficient square. -/
def schoberLowSymm (n : ℕ) (A : PowerSeries (PowerSeries ℂ)) : Prop :=
  ∀ i j : ℕ, i < n → j < n →
    schoberBiCoeff i j A = schoberBiCoeff j i A

/-- The two-variable Cauchy product, with the first coefficient index
belonging to the inner power series. -/
theorem schoberBiCoeff_mul
    (A B : PowerSeries (PowerSeries ℂ)) (i j : ℕ) :
    schoberBiCoeff i j (A * B) =
      ∑ p ∈ Finset.range (j + 1),
        ∑ q ∈ Finset.range (i + 1),
          schoberBiCoeff q p A *
            schoberBiCoeff (i - q) (j - p) B := by
  unfold schoberBiCoeff
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem schoberLowSymm_mul {n : ℕ}
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA : schoberLowSymm n A) (hB : schoberLowSymm n B) :
    schoberLowSymm n (A * B) := by
  intro i j hi hj
  rw [schoberBiCoeff_mul, schoberBiCoeff_mul]
  calc
    (∑ p ∈ Finset.range (j + 1),
        ∑ q ∈ Finset.range (i + 1),
          schoberBiCoeff q p A *
            schoberBiCoeff (i - q) (j - p) B) =
      ∑ q ∈ Finset.range (i + 1),
        ∑ p ∈ Finset.range (j + 1),
          schoberBiCoeff q p A *
            schoberBiCoeff (i - q) (j - p) B := by
        exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro p hp
      simp only [Finset.mem_range] at hq hp
      have hq' : q ≤ i := by omega
      have hp' : p ≤ j := by omega
      rw [hA q p (by omega) (by omega),
        hB (i - q) (j - p) (by omega) (by omega)]

theorem schoberLowSymm_add {n : ℕ}
    {A B : PowerSeries (PowerSeries ℂ)}
    (hA : schoberLowSymm n A) (hB : schoberLowSymm n B) :
    schoberLowSymm n (A + B) := by
  intro i j hi hj
  change PowerSeries.coeff i (PowerSeries.coeff j (A + B)) =
    PowerSeries.coeff j (PowerSeries.coeff i (A + B))
  simpa only [map_add, schoberBiCoeff] using
    congrArg₂ (· + ·) (hA i j hi hj) (hB i j hi hj)

theorem schoberLowSymm_const_mul {n : ℕ}
    (c : ℂ) {A : PowerSeries (PowerSeries ℂ)}
    (hA : schoberLowSymm n A) :
    schoberLowSymm n (PowerSeries.C (PowerSeries.C c) * A) := by
  intro i j hi hj
  simp only [schoberBiCoeff, PowerSeries.coeff_C_mul]
  exact congrArg (fun z : ℂ => c * z) (hA i j hi hj)

theorem schoberLowSymm_pow {n : ℕ}
    {A : PowerSeries (PowerSeries ℂ)}
    (hA : schoberLowSymm n A) (k : ℕ) (hk : 1 ≤ k) :
    schoberLowSymm n (A ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  induction m with
  | zero => simpa using hA
  | succ m ih =>
    rw [pow_succ]
    exact schoberLowSymm_mul (ih (by omega)) hA

end SpringerLean
