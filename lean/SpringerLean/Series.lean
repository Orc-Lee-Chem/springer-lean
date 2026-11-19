import SpringerLean.Catalan
import SpringerLean.Analytic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum

namespace SpringerLean

/-- The manuscript's Catalan numbers have a geometric majorant. -/
theorem catalan_le_four_pow (k : ℕ) : catalan k ≤ 4 ^ k := by
  rw [catalan_eq_centralBinom_div]
  exact (Nat.div_le_self _ _).trans (Nat.centralBinom_le_four_pow k)

/-- A norm bound for the odd inverse coefficients of a rotated slit. -/
theorem slitOddCoeff_norm_le (a : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    ‖slitOddCoeff a k‖ ≤ (4 : ℝ) ^ k := by
  have h : ‖slitOddCoeff a k‖ = (catalan k : ℝ) := by
    simp [slitOddCoeff, norm_pow, ha]
  rw [h]
  exact_mod_cast catalan_le_four_pow k

/-- The numerical Catalan correction series. -/
noncomputable def slitQ (a u : ℂ) : ℂ :=
  ∑' k : ℕ, slitOddCoeff a k * u ^ k

private theorem slitQ_term_bound (a u : ℂ) (ha : ‖a‖ = 1) (k : ℕ) :
    ‖slitOddCoeff a k * u ^ k‖ ≤ ((4 : ℝ) * ‖u‖) ^ k := by
  calc
    ‖slitOddCoeff a k * u ^ k‖ = ‖slitOddCoeff a k‖ * ‖u‖ ^ k := by
      rw [norm_mul, norm_pow]
    _ ≤ (4 : ℝ) ^ k * ‖u‖ ^ k :=
      mul_le_mul_of_nonneg_right (slitOddCoeff_norm_le a ha k) (pow_nonneg (norm_nonneg _) _)
    _ = ((4 : ℝ) * ‖u‖) ^ k := by rw [mul_pow]

/-- Absolute convergence throughout `‖u‖ < 1/4`. -/
theorem slitQ_summable_norm (a u : ℂ) (ha : ‖a‖ = 1)
    (hu : ‖u‖ < 1 / 4) :
    Summable (fun k : ℕ => ‖slitOddCoeff a k * u ^ k‖) := by
  have hr : (4 : ℝ) * ‖u‖ < 1 := by nlinarith
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (slitQ_term_bound a u ha)
    (summable_geometric_of_lt_one (by positivity) hr)

theorem slitQ_hasSum (a u : ℂ) (ha : ‖a‖ = 1)
    (hu : ‖u‖ < 1 / 4) :
    HasSum (fun k : ℕ => slitOddCoeff a k * u ^ k) (slitQ a u) := by
  exact (slitQ_summable_norm a u ha hu).of_norm.hasSum

/-- A directly reusable geometric upper bound for the numerical sum. -/
theorem slitQ_norm_le (a u : ℂ) (ha : ‖a‖ = 1)
    (hu : ‖u‖ < 1 / 4) :
    ‖slitQ a u‖ ≤ (1 - 4 * ‖u‖)⁻¹ := by
  have hr : (4 : ℝ) * ‖u‖ < 1 := by nlinarith
  have hg := hasSum_geometric_of_lt_one (by positivity : 0 ≤ (4 : ℝ) * ‖u‖) hr
  exact (slitQ_hasSum a u ha hu).norm_le_of_bounded hg (slitQ_term_bound a u ha)


/-- The formal Catalan recurrence becomes a numerical identity on its disk of convergence. -/
theorem slitQ_quadratic (a u : ℂ) (ha : ‖a‖ = 1)
    (hu : ‖u‖ < 1 / 4) : slitQ a u = a + u * (slitQ a u) ^ 2 := by
  let f : ℕ → ℂ := fun k => slitOddCoeff a k * u ^ k
  have hf : Summable f := (slitQ_summable_norm a u ha hu).of_norm
  have hfn : Summable (fun k => ‖f k‖) := slitQ_summable_norm a u ha hu
  have hinner (n : ℕ) :
      (∑ ij ∈ Finset.antidiagonal n, f ij.1 * f ij.2) =
        slitOddCoeff a (n + 1) * u ^ n := by
    rw [slitOddCoeff_succ_antidiagonal, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    have hijsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    change (slitOddCoeff a ij.1 * u ^ ij.1) *
      (slitOddCoeff a ij.2 * u ^ ij.2) =
      (slitOddCoeff a ij.1 * slitOddCoeff a ij.2) * u ^ n
    rw [← hijsum, pow_add]
    ring
  have hsq : slitQ a u * slitQ a u =
      ∑' n : ℕ, slitOddCoeff a (n + 1) * u ^ n := by
    have hc := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hfn
    change slitQ a u * slitQ a u =
      ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n, f ij.1 * f ij.2 at hc
    simpa only [hinner] using hc
  have hshift : slitQ a u = slitOddCoeff a 0 +
      ∑' n : ℕ, slitOddCoeff a (n + 1) * u ^ (n + 1) := by
    simpa only [slitQ, f, pow_zero, mul_one] using hf.tsum_eq_zero_add
  calc
    slitQ a u = slitOddCoeff a 0 +
        ∑' n : ℕ, slitOddCoeff a (n + 1) * u ^ (n + 1) := hshift
    _ = a + u * (∑' n : ℕ, slitOddCoeff a (n + 1) * u ^ n) := by
      rw [slitOddCoeff_zero, ← tsum_mul_left]
      congr 1
      apply tsum_congr
      intro n
      rw [pow_succ]
      ring
    _ = a + u * (slitQ a u) ^ 2 := by rw [pow_two, hsq]

/-- A convenient uniform bound for the substitution `u=t²`, `‖t‖<1/4`. -/
theorem slitQ_norm_le_four_thirds (a t : ℂ) (ha : ‖a‖ = 1)
    (ht : ‖t‖ < 1 / 4) : ‖slitQ a (t ^ 2)‖ ≤ (4 : ℝ) / 3 := by
  have ht0 : 0 ≤ ‖t‖ := norm_nonneg _
  have hsquare : ‖t‖ ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    have hp : 0 < ((1 / 4 : ℝ) - ‖t‖) * ((1 / 4 : ℝ) + ‖t‖) := by
      apply mul_pos <;> nlinarith
    nlinarith
  have hu : ‖t ^ 2‖ < 1 / 4 := by
    rw [norm_pow]
    nlinarith
  have hden : (3 / 4 : ℝ) ≤ 1 - 4 * ‖t ^ 2‖ := by
    rw [norm_pow]
    nlinarith
  calc
    ‖slitQ a (t ^ 2)‖ ≤ (1 - 4 * ‖t ^ 2‖)⁻¹ := slitQ_norm_le a (t ^ 2) ha hu
    _ ≤ (4 : ℝ) / 3 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 3 / 4 by norm_num) hden
      convert h using 1 <;> norm_num
end SpringerLean