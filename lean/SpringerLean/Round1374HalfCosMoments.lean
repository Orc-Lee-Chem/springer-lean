import SpringerLean.Round1351CircleSinMoment
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

namespace SpringerLean
set_option maxHeartbeats 30000

noncomputable def halfCosMoment (n : ℕ) : ℝ :=
  ∫ θ in (0:ℝ)..Real.pi/2, Real.cos θ ^ n

/-- The one-dimensional half-circle cosine recurrence. -/
theorem halfCosMoment_succ_succ (n : ℕ) :
    halfCosMoment (n+2) =
      ((n+1:ℕ):ℝ)/((n+2:ℕ):ℝ) * halfCosMoment n := by
  unfold halfCosMoment
  rw [integral_cos_pow (a := (0:ℝ)) (b := Real.pi/2) n]
  have hzero : (0:ℝ)^(n+1)=0 := by
    rw [pow_succ]
    ring
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two,
    Real.cos_zero, Real.sin_zero, hzero, one_pow,
    mul_zero, sub_zero, zero_div, zero_add]
  push_cast
  ring

/-- The weighted sine-square moment is exactly one part in `n+2`. -/
theorem halfCosMoment_sin_sq (n : ℕ) :
    (∫ θ in (0:ℝ)..Real.pi/2,
      Real.cos θ ^ n * Real.sin θ ^ 2) =
      halfCosMoment n / ((n+2:ℕ):ℝ) := by
  have hpoint (θ : ℝ) : Real.cos θ ^ n * Real.sin θ ^ 2 =
      Real.cos θ ^ n - Real.cos θ ^ (n+2) := by
    rw [Real.sin_sq]
    rw [pow_add]
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_sub]
  · change halfCosMoment n - halfCosMoment (n+2) = _
    rw [halfCosMoment_succ_succ]
    have hden : ((n+2:ℕ):ℝ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  all_goals apply Continuous.intervalIntegrable <;> fun_prop

/-- The comparison circle's normalization is `2^(n+1) C_n/π`;
the factor `1/2` for a positive semicircle is explicit. -/
theorem comparisonCircleMoment_eq_halfCosMoment (n : ℕ) :
    Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 =
      (2:ℝ)^(n+1)/Real.pi * halfCosMoment n := by
  rw [comparisonCircleMoment_eq_sinMoment]
  unfold comparisonSinMoment halfCosMoment
  have hC := EulerSine.integral_cos_pow_eq n
  have hSin : (∫ θ in (0:ℝ)..Real.pi, Real.sin θ ^ n) =
      2*(∫ θ in (0:ℝ)..Real.pi/2, Real.cos θ ^ n) := by
    linarith
  rw [hSin, pow_succ]
  ring

end SpringerLean

#print axioms SpringerLean.halfCosMoment_succ_succ
#print axioms SpringerLean.halfCosMoment_sin_sq
#print axioms SpringerLean.comparisonCircleMoment_eq_halfCosMoment
