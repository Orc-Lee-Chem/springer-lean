import SpringerLean.Round1808PositiveDiskMomentStep
import SpringerLean.Round1798TrueAxisLambdaLog

namespace SpringerLean
set_option maxHeartbeats 900000

theorem trueAxisMomentRatioLambda_explicit (m : ℝ) :
    trueAxisMomentRatioLambda m=((m-1)/m)*((m-1)/(m+2))*
      ((m-3)/m)*((m-5)/(m-2))*((m-7)/(m-4)) := by
  unfold trueAxisMomentRatioLambda
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, mul_zero, sub_zero, mul_one, one_mul]
  ring

theorem trueAxisMomentRatioLambda_reference_even (q : ℕ) (hq : 1 ≤ q) :
    trueAxisMomentRatioLambda (2*(q : ℝ)+8)*comparisonPositiveDiskMoment (2*q)=
      (1-1/(2*(q : ℝ)+8))*comparisonPositiveDiskMoment (2*q+8) := by
  have hstep (j : ℕ) : comparisonPositiveDiskMoment (2*q+2*j+2)=
      ((2*(q : ℝ)+2*(j : ℝ)+1)/(2*(q : ℝ)+2*(j : ℝ)+4))*
        comparisonPositiveDiskMoment (2*q+2*j) := by
    have hh := comparisonPositiveDiskMoment_even_step_solved (q+j) (by omega : 1 ≤ q+j)
    rw [show 2*(q+j)=2*q+2*j by omega] at hh
    have hn : 2*((q+j : ℕ) : ℝ)+1=2*(q : ℝ)+2*(j : ℝ)+1 := by push_cast; ring
    have hd : 2*((q+j : ℕ) : ℝ)+4=2*(q : ℝ)+2*(j : ℝ)+4 := by push_cast; ring
    rw [hn,hd] at hh
    exact hh
  have h₀ := hstep 0
  have h₁ := hstep 1
  have h₂ := hstep 2
  have h₃ := hstep 3
  norm_num [Nat.add_assoc,add_assoc] at h₀ h₁ h₂ h₃
  rw [h₃,h₂,h₁,h₀,trueAxisMomentRatioLambda_explicit]
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hfirst : (2*(q : ℝ)+8-1)/(2*(q : ℝ)+8)=1-1/(2*(q : ℝ)+8) := by
    field_simp
    <;> ring
  rw [hfirst]
  ring

/-- The actual true-axis test has exactly the advertised uncut model
cost (1-1/m)M_m, in the same disk normalization. -/
theorem trueAxisMomentRatioLambda_reference
    (k : ℕ) (hk : 751 ≤ k) :
    trueAxisMomentRatioLambda ((2*k-2 : ℕ) : ℝ)*comparisonPositiveDiskMoment (2*k-10)=
      (1-1/((2*k-2 : ℕ) : ℝ))*comparisonPositiveDiskMoment (2*k-2) := by
  have hh := trueAxisMomentRatioLambda_reference_even (k-5) (by omega : 1 ≤ k-5)
  have hi : 2*(k-5)=2*k-10 := by omega
  have hi' : 2*(k-5)+8=2*k-2 := by omega
  have hc : 2*((k-5 : ℕ) : ℝ)+8=((2*k-2 : ℕ) : ℝ) := by
    exact_mod_cast hi'
  simpa only [hi,hi',hc, show 2*k-10+8=2*k-2 by omega] using hh

end SpringerLean

#print axioms SpringerLean.trueAxisMomentRatioLambda_reference
