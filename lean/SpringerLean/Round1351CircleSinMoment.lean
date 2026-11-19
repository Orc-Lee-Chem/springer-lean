import SpringerLean.Round1350SinMomentScalar
import SpringerLean.Round30AnglePair

open MeasureTheory

namespace SpringerLean

/-- One full period of an absolute sine power is twice its positive
half-period integral. -/
theorem integral_abs_sin_pow_full_eq_two (n : ℕ) :
    (∫ θ in (0:ℝ)..2*Real.pi, |Real.sin θ|^n) =
      2 * (∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ n) := by
  let f : ℝ → ℝ := fun θ => |Real.sin θ|^n
  have hper : Function.Periodic f (2*Real.pi) := by
    intro θ
    simp [f, Real.sin_add_two_pi]
  have hint : IntervalIntegrable f volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    fun_prop
  have hpair := periodic_angle_integral_pair f hper hint
  have hneg (θ : ℝ) : f (-θ)=f θ := by simp [f, Real.sin_neg]
  simp_rw [hneg] at hpair
  have hpositive :
      (∫ θ in (0:ℝ)..Real.pi, f θ) =
      ∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ n := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp [f]
    have hθ' : θ ∈ Set.Icc (0:ℝ) Real.pi := by
      simpa [Set.uIcc_of_le Real.pi_pos.le] using hθ
    rw [abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hθ')]
  have hhalfInt : IntervalIntegrable f volume (0:ℝ) Real.pi := by
    apply Continuous.intervalIntegrable
    dsimp [f]
    fun_prop
  rw [hpair, intervalIntegral.integral_add hhalfInt hhalfInt,
    hpositive]
  ring

/-- The comparison variable has the *circle* law, with the project
normalization `Real.circleAverage`; the disk-area semicircle law is
not used here. -/
theorem comparisonCircleMoment_eq_sinMoment (n : ℕ) :
    Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1 = comparisonSinMoment n := by
  rw [Real.circleAverage_eq_integral_add (Real.pi/2)]
  simp_rw [circleMap_zero_re]
  simp only [one_mul, Real.cos_add_pi_div_two, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<2), abs_neg]
  have hform :
      (∫ θ in (0:ℝ)..2*Real.pi,
        (2*|Real.sin θ|)^n) =
      (2:ℝ)^n * (∫ θ in (0:ℝ)..2*Real.pi,
        |Real.sin θ|^n) := by
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul]
  rw [hform, integral_abs_sin_pow_full_eq_two]
  unfold comparisonSinMoment
  simp only [div_eq_mul_inv]
  ring

/-- The exact normalized circle ratio required by a weak Catalan
candidate follows from the sine reduction formula. -/
theorem comparisonCircleMoment_succ_half_ge
    (n : ℕ) (hn : 1 ≤ n) :
    (1-1/(n:ℝ)) *
      Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 ≤
      Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^(n+1)) 0 1 / 2 := by
  rw [comparisonCircleMoment_eq_sinMoment,
    comparisonCircleMoment_eq_sinMoment]
  exact comparisonSinMoment_succ_half_ge n hn

end SpringerLean

#print axioms SpringerLean.integral_abs_sin_pow_full_eq_two
#print axioms SpringerLean.comparisonCircleMoment_eq_sinMoment
#print axioms SpringerLean.comparisonCircleMoment_succ_half_ge
