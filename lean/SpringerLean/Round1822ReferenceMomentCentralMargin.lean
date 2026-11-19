import SpringerLean.Round1808PositiveDiskMomentStep
import SpringerLean.Round1772CentralExponentialBudget

open MeasureTheory Metric

namespace SpringerLean
set_option maxHeartbeats 800000

theorem comparisonPositiveDiskMoment_nonneg (m : ℕ) :
    0 ≤ comparisonPositiveDiskMoment m := by
  unfold comparisonPositiveDiskMoment
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun x => pow_nonneg (le_max_right _ _) _)

/-- A deliberately coarse elementary moment lower bound suffices to
pay the fixed central allowance in the true-axis phase branch. -/
theorem comparisonPositiveDiskMoment_even_square_lower (q : ℕ) (hq : 1 ≤ q) :
    1 ≤ 8*(q : ℝ)^2*comparisonPositiveDiskMoment (2*q) := by
  induction q,hq using Nat.le_induction with
  | base =>
    have hh := comparisonPositiveDiskMoment_catalan (k := 2) (by norm_num)
    norm_num [catalan_succ] at hh ⊢
    linarith
  | succ q hq ih =>
    have hstep := comparisonPositiveDiskMoment_even_step q hq
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hM := comparisonPositiveDiskMoment_nonneg (2*q)
    have hcoef : (2*(q : ℝ)+4)*(q : ℝ)^2 ≤ (2*(q : ℝ)+1)*((q : ℝ)+1)^2 := by
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoef hM
    have hih := mul_le_mul_of_nonneg_left ih (show 0 ≤ 2*(q : ℝ)+4 by positivity)
    have hrec := congrArg (fun r : ℝ => 8*((q : ℝ)+1)^2*r) hstep
    have hh : 1 ≤ 8*((q : ℝ)+1)^2*comparisonPositiveDiskMoment (2*q+2) := by
      nlinarith [hrec,hmul,hih]
    simpa only [Nat.cast_add,Nat.cast_one,show 2*(q+1)=2*q+2 by omega] using hh

theorem central_allowance_lt_trueAxis_margin (k : ℕ) (hk : 751 ≤ k) :
    (23/25 : ℝ)^(2*k-2) <
      comparisonPositiveDiskMoment (2*k-2)/((2*k-2 : ℕ) : ℝ) := by
  let m := 2*k-2
  have hm : 1500 ≤ m := by dsimp [m]; omega
  have hm' : (1500 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hM := comparisonPositiveDiskMoment_even_square_lower (k-1) (by omega : 1 ≤ k-1)
  have hi : 2*(k-1)=m := by dsimp [m]; omega
  have hcast : 2*((k-1 : ℕ) : ℝ)=(m : ℝ) := by exact_mod_cast hi
  rw [hi] at hM
  have hM' : 1 ≤ 2*(m : ℝ)^2*comparisonPositiveDiskMoment m := by
    rw [←hcast]
    nlinarith [hM]
  have hpow : 2 ≤ (m : ℝ)^5 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show (2 : ℝ) ≤ m by linarith) 5
    nlinarith
  have hcoef : 2*(m : ℝ)^3 ≤ (m : ℝ)^8 := by
    nlinarith [mul_le_mul_of_nonneg_right hpow (show 0 ≤ (m : ℝ)^3 by positivity)]
  have hg := central_geometric_budget hm
  have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ (23/25 : ℝ)^m by positivity)
  have hsmall : 2*(m : ℝ)^3*(23/25 : ℝ)^m < 1 := by nlinarith
  change (23/25 : ℝ)^m < comparisonPositiveDiskMoment m/(m : ℝ)
  apply (lt_div_iff₀ hm0).mpr
  nlinarith

end SpringerLean

#print axioms SpringerLean.central_allowance_lt_trueAxis_margin
