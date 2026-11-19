import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace SpringerLean

/-- The reference circle moment, expressed through the positive sine
integral. A separate angular-symmetry lemma identifies this with
`circleAverage |2 Re ζ|^n`. -/
noncomputable def comparisonSinMoment (n : ℕ) : ℝ :=
  (2:ℝ)^n / Real.pi *
    (∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ n)

/-- The elementary sine reduction already gives the exact candidate
ratio needed for the two-end contradiction. -/
theorem comparisonSinMoment_succ_half_ge
    (n : ℕ) (hn : 1 ≤ n) :
    (1-1/(n:ℝ))*comparisonSinMoment n ≤
      comparisonSinMoment (n+1)/2 := by
  let S : ℕ → ℝ := fun j => ∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ j
  have hrec := integral_sin_pow (a := (0:ℝ)) (b := Real.pi) n
  have hrec' : S (n+2) = ((n:ℝ)+1)/((n:ℝ)+2)*S n := by
    simpa [S, Real.sin_zero, Real.sin_pi] using hrec
  have hmono : S (n+2) ≤ S (n+1) := integral_sin_pow_succ_le (n+1)
  have hS0 : 0 ≤ S n := (integral_sin_pow_pos n).le
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hratio : 1-1/(n:ℝ) ≤ ((n:ℝ)+1)/((n:ℝ)+2) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<(n:ℝ)+2)).2
    field_simp
    nlinarith
  have hS : (1-1/(n:ℝ))*S n ≤ S (n+1) := by
    calc
      _ ≤ (((n:ℝ)+1)/((n:ℝ)+2))*S n :=
        mul_le_mul_of_nonneg_right hratio hS0
      _ = S (n+2) := hrec'.symm
      _ ≤ S (n+1) := hmono
  have hfactor : 0 ≤ (2:ℝ)^n/Real.pi := by positivity
  have h := mul_le_mul_of_nonneg_left hS hfactor
  change (1-1/(n:ℝ))*((2:ℝ)^n/Real.pi*S n) ≤
    ((2:ℝ)^(n+1)/Real.pi*S (n+1))/2
  calc
    (1-1/(n:ℝ))*((2:ℝ)^n/Real.pi*S n) =
        ((2:ℝ)^n/Real.pi)*((1-1/(n:ℝ))*S n) := by ring
    _ ≤ ((2:ℝ)^n/Real.pi)*S (n+1) := h
    _ = ((2:ℝ)^(n+1)/Real.pi*S (n+1))/2 := by
      rw [pow_succ]
      ring

end SpringerLean

#print axioms SpringerLean.comparisonSinMoment_succ_half_ge
