import SpringerLean.Slit
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.RingTheory.PowerSeries.Basic

namespace SpringerLean

/-- Coefficient of `w ^ (-(2*k+1))` in `w - J_a⁻¹(w)`. -/
def slitOddCoeff (a : ℂ) (k : ℕ) : ℂ := a ^ (k + 1) * (catalan k : ℂ)

theorem slitOddCoeff_zero (a : ℂ) : slitOddCoeff a 0 = a := by
  simp [slitOddCoeff, catalan_zero]

theorem slitOddCoeff_succ (a : ℂ) (k : ℕ) :
    slitOddCoeff a (k + 1) =
      ∑ i : Fin (k + 1), slitOddCoeff a i * slitOddCoeff a (k - i) := by
  simp only [slitOddCoeff, catalan_succ, Nat.cast_sum, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i : ℕ) ≤ k := by omega
  have hex : (i : ℕ) + 1 + (k - (i : ℕ) + 1) = k + 2 := by omega
  have hpow : a ^ (k + 1 + 1) = a ^ ((i : ℕ) + 1) * a ^ (k - (i : ℕ) + 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  ring

/-- The inverse-correction series in u=t²; term k gives w^(-(2k+1)). -/
noncomputable def slitCorrection (a : ℂ) : PowerSeries ℂ := PowerSeries.mk (slitOddCoeff a)

theorem slitCorrection_coeff (a : ℂ) (k : ℕ) :
    PowerSeries.coeff k (slitCorrection a) = slitOddCoeff a k := by
  simp [slitCorrection]


theorem slitOddCoeff_succ_antidiagonal (a : ℂ) (k : ℕ) :
    slitOddCoeff a (k + 1) =
      ∑ ij ∈ Finset.antidiagonal k,
        slitOddCoeff a ij.1 * slitOddCoeff a ij.2 := by
  rw [slitOddCoeff_succ]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun x y => slitOddCoeff a x * slitOddCoeff a y) k]
  rw [Finset.sum_range]

/-- The Catalan recurrence is the exact formal quadratic inverse equation. -/
theorem slitCorrection_quadratic (a : ℂ) :
    slitCorrection a = PowerSeries.C a +
      PowerSeries.X * (slitCorrection a * slitCorrection a) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [slitCorrection_coeff, slitOddCoeff_zero]
  | succ k =>
      rw [map_add, slitCorrection_coeff]
      rw [PowerSeries.coeff_C_of_ne_zero (Nat.succ_ne_zero k), zero_add]
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul]
      simpa only [slitCorrection_coeff] using slitOddCoeff_succ_antidiagonal a k

/-- The normalized formal inverse branch solves the same quadratic equation. -/
theorem slitCorrection_normalized_inverse (a : ℂ) :
    let p := slitCorrection a
    (1 - PowerSeries.X * p) * (1 - PowerSeries.X * p) +
      PowerSeries.C a * PowerSeries.X = 1 - PowerSeries.X * p := by
  dsimp
  have heq : PowerSeries.C a + PowerSeries.X * (slitCorrection a * slitCorrection a) =
      slitCorrection a := (slitCorrection_quadratic a).symm
  calc
    (1 - PowerSeries.X * slitCorrection a) *
        (1 - PowerSeries.X * slitCorrection a) +
        PowerSeries.C a * PowerSeries.X =
      (1 - PowerSeries.X * slitCorrection a) +
        PowerSeries.X * (PowerSeries.C a +
          PowerSeries.X * (slitCorrection a * slitCorrection a) - slitCorrection a) := by ring
    _ = 1 - PowerSeries.X * slitCorrection a := by rw [heq]; ring

/-- The quadratic equation determines a unique formal correction series. -/
theorem slitCorrection_unique (a : ℂ) (q : PowerSeries ℂ)
    (hq : q = PowerSeries.C a + PowerSeries.X * (q * q)) :
    q = slitCorrection a := by
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          have hc := congrArg (PowerSeries.coeff 0) hq
          simpa [slitCorrection_coeff, slitOddCoeff_zero] using hc
      | succ k =>
          have hc := congrArg (PowerSeries.coeff (k + 1)) hq
          rw [map_add, PowerSeries.coeff_C_of_ne_zero (Nat.succ_ne_zero k),
            zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mul] at hc
          rw [hc, slitCorrection_coeff, slitOddCoeff_succ_antidiagonal]
          apply Finset.sum_congr rfl
          intro ij hij
          have hs : ij.1 + ij.2 = k := Finset.mem_antidiagonal.mp hij
          have h1 : ij.1 < k + 1 := by omega
          have h2 : ij.2 < k + 1 := by omega
          rw [ih ij.1 h1, ih ij.2 h2, slitCorrection_coeff, slitCorrection_coeff]
end SpringerLean