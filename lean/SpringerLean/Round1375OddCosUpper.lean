import SpringerLean.Round1374HalfCosMoments
import Mathlib.Analysis.Real.Pi.Bounds

namespace SpringerLean

noncomputable def normalizedHalfCosMoment (n : ℕ) : ℝ :=
  (2/Real.pi)*halfCosMoment n

theorem normalizedHalfCosMoment_pos (n : ℕ) :
    0 < normalizedHalfCosMoment n := by
  unfold normalizedHalfCosMoment halfCosMoment
  exact mul_pos (div_pos (by norm_num) Real.pi_pos)
    (EulerSine.integral_cos_pow_pos n)

theorem normalizedHalfCosMoment_succ_succ (n : ℕ) :
    normalizedHalfCosMoment (n+2) =
      ((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ)*normalizedHalfCosMoment n := by
  unfold normalizedHalfCosMoment
  rw [halfCosMoment_succ_succ]
  ring

/-- The sharpened odd cosine moment induction. Its square-form
recurrence uses `(n+1)(n+3)≤(n+2)²`. -/
theorem normalizedHalfCosMoment_odd_sq_upper (k : ℕ) :
    normalizedHalfCosMoment (2*k+1)^2 ≤
      1/(((2*k+2:ℕ):ℝ)) := by
  induction k with
  | zero =>
      have hC1 : halfCosMoment 1 = 1 := by
        unfold halfCosMoment
        simp [integral_cos]
      have hπ3 := Real.pi_gt_three
      have hπpos := Real.pi_pos
      have hπsq : (8:ℝ) ≤ Real.pi^2 := by nlinarith
      have hden : 0 < Real.pi^2 := sq_pos_of_pos hπpos
      have hratio : (4:ℝ)/Real.pi^2 ≤ 1/2 := by
        apply (div_le_iff₀ hden).2
        nlinarith
      simpa [normalizedHalfCosMoment, hC1, div_pow,
        show (2:ℝ)^2=4 by norm_num] using hratio
  | succ k ih =>
      let n : ℕ := 2*k+1
      have hn0 : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
      have hn2 : (0:ℝ) < ((n+2:ℕ):ℝ) := by positivity
      have hn3 : (0:ℝ) < ((n+3:ℕ):ℝ) := by positivity
      have hrec := normalizedHalfCosMoment_succ_succ n
      have hindex : 2*(k+1)+1=n+2 := by dsimp [n]; omega
      have hindexDen : 2*(k+1)+2=n+3 := by dsimp [n]; omega
      rw [hindex,hindexDen,hrec]
      have hOld : normalizedHalfCosMoment n^2 ≤ 1/((n+1:ℕ):ℝ) := by
        have hidx : 2*k+2=n+1 := by dsimp [n]
        rw [← hidx]
        exact ih
      have hratio : ((n+1:ℕ):ℝ)^2 / ((n+2:ℕ):ℝ)^2 *
          (1/((n+1:ℕ):ℝ)) ≤ 1/((n+3:ℕ):ℝ) := by
        have hsqden : 0 < (((n+2:ℕ):ℝ))^2 := sq_pos_of_pos hn2
        have hpoly : ((n+1:ℕ):ℝ)*((n+3:ℕ):ℝ) ≤
            (((n+2:ℕ):ℝ))^2 := by
          push_cast
          nlinarith
        have hdiv : ((n+1:ℕ):ℝ)/(((n+2:ℕ):ℝ))^2 ≤
            1/((n+3:ℕ):ℝ) := by
          apply (div_le_div_iff₀ hsqden hn3).2
          nlinarith [hpoly]
        have hne : ((n+1:ℕ):ℝ) ≠ 0 := hn0.ne'
        convert hdiv using 1 <;> field_simp
      have hmul := mul_le_mul_of_nonneg_left hOld
        (sq_nonneg (((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ)))
      calc
        (((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ)*
          normalizedHalfCosMoment n)^2 =
            (((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ))^2 *
              normalizedHalfCosMoment n^2 := by ring
        _ ≤ (((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ))^2 *
              (1/((n+1:ℕ):ℝ)) := hmul
        _ = ((n+1:ℕ):ℝ)^2 / ((n+2:ℕ):ℝ)^2 *
              (1/((n+1:ℕ):ℝ)) := by ring
        _ ≤ 1/((n+3:ℕ):ℝ) := hratio

/-- The odd comparison-circle moment has a slightly stronger bound
than the `2^n/√n` needed by the chord saving. -/
theorem comparisonCircleMoment_odd_upper (k : ℕ) :
    Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^(2*k+1)) 0 1 ≤
      (2:ℝ)^(2*k+1)/Real.sqrt (((2*k+2:ℕ):ℝ)) := by
  let n : ℕ := 2*k+1
  have hsq := normalizedHalfCosMoment_odd_sq_upper k
  have hcnonneg : 0 ≤ normalizedHalfCosMoment n :=
    (normalizedHalfCosMoment_pos n).le
  have hsqrt : 0 < Real.sqrt (((2*k+2:ℕ):ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have hsqroot : (1/Real.sqrt (((2*k+2:ℕ):ℝ)))^2 =
      1/(((2*k+2:ℕ):ℝ)) := by
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]
    simp only [one_div]
  have hcbound : normalizedHalfCosMoment n ≤
      1/Real.sqrt (((2*k+2:ℕ):ℝ)) := by
    change normalizedHalfCosMoment n^2 ≤
      1/(((2*k+2:ℕ):ℝ)) at hsq
    have ha0 : 0 ≤ 1/Real.sqrt (((2*k+2:ℕ):ℝ)) := by positivity
    have hsqle : normalizedHalfCosMoment n^2 ≤
        (1/Real.sqrt (((2*k+2:ℕ):ℝ)))^2 := by
      rw [hsqroot]
      exact hsq
    nlinarith
  have hnorm : Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1 =
      (2:ℝ)^n*normalizedHalfCosMoment n := by
    rw [comparisonCircleMoment_eq_halfCosMoment]
    unfold normalizedHalfCosMoment
    rw [pow_succ]
    ring
  change Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 ≤ _
  rw [hnorm]
  have hmul := mul_le_mul_of_nonneg_left hcbound
    (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n)
  simpa [n, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem comparisonCircleMoment_odd_le_two_pow_div_sqrt (k : ℕ) :
    Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^(2*k+1)) 0 1 ≤
      (2:ℝ)^(2*k+1)/Real.sqrt (((2*k+1:ℕ):ℝ)) := by
  have hstrong := comparisonCircleMoment_odd_upper k
  have hn0 : (0:ℝ) < ((2*k+1:ℕ):ℝ) := by positivity
  have hs0 : 0 < Real.sqrt (((2*k+1:ℕ):ℝ)) := Real.sqrt_pos.2 hn0
  have hs1 : 0 < Real.sqrt (((2*k+2:ℕ):ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  have hroots : Real.sqrt (((2*k+1:ℕ):ℝ)) ≤
      Real.sqrt (((2*k+2:ℕ):ℝ)) :=
    Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 2*k+1 ≤ 2*k+2))
  have hdiv : (2:ℝ)^(2*k+1)/Real.sqrt (((2*k+2:ℕ):ℝ)) ≤
      (2:ℝ)^(2*k+1)/Real.sqrt (((2*k+1:ℕ):ℝ)) := by
    apply (div_le_div_iff₀ hs1 hs0).2
    exact mul_le_mul_of_nonneg_left hroots (by positivity)
  exact hstrong.trans hdiv

end SpringerLean

#print axioms SpringerLean.normalizedHalfCosMoment_odd_sq_upper
#print axioms SpringerLean.comparisonCircleMoment_odd_upper
#print axioms SpringerLean.comparisonCircleMoment_odd_le_two_pow_div_sqrt
