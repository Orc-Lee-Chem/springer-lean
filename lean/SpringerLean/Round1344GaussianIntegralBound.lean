import SpringerLean.Round1343GaussianPointwise
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory

namespace SpringerLean

/-- Restricting the positive Gaussian to the principal circle interval
cannot increase its integral. -/
theorem gaussian_principal_interval_le (b : ℝ) (hb : 0 < b) :
    (∫ θ in -Real.pi..Real.pi, Real.exp (-b*θ^2)) ≤
      Real.sqrt (Real.pi/b) := by
  rw [intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by
    linarith [Real.pi_pos])]
  exact (setIntegral_le_integral
    (integrable_exp_neg_mul_sq hb)
    (Filter.Eventually.of_forall (fun θ => (Real.exp_pos _).le))).trans_eq
      (integral_gaussian b)

/-- The entire coarse one-end comparison-circle cost is bounded by a
platform term and one elementary Gaussian integral. -/
theorem affinePlatform_principal_integral_le
    (n : ℕ) (hn : 1 ≤ n) :
    (∫ θ in -Real.pi..Real.pi,
      (max (39/20 : ℝ) ((2/5)+(8/5)*Real.cos θ))^n) ≤
      (2*Real.pi)*(39/20 : ℝ)^n + (2:ℝ)^n *
        Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) := by
  let b : ℝ := (n:ℝ)*(8/5)/Real.pi^2
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hpoint : ∀ θ ∈ Set.Icc (-Real.pi) Real.pi,
      (max (39/20 : ℝ) ((2/5)+(8/5)*Real.cos θ))^n ≤
        (39/20 : ℝ)^n + (2:ℝ)^n*Real.exp (-b*θ^2) := by
    intro θ hθ
    have hθabs : |θ| ≤ Real.pi := abs_le.mpr hθ
    convert affinePlatformPower_le_gaussian n hn hθabs using 1
    dsimp [b]
    ring
  have hFint : IntervalIntegrable
      (fun θ : ℝ => (max (39/20 : ℝ) ((2/5)+(8/5)*Real.cos θ))^n)
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hGint : IntervalIntegrable
      (fun θ : ℝ => (39/20 : ℝ)^n + (2:ℝ)^n*Real.exp (-b*θ^2))
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hpi hFint hGint hpoint
  have hgauss := gaussian_principal_interval_le b hb
  have hCint : IntervalIntegrable (fun _ : ℝ => (39/20 : ℝ)^n)
      volume (-Real.pi) Real.pi := by
    exact continuous_const.intervalIntegrable _ _
  have hEint : IntervalIntegrable
      (fun θ : ℝ => (2:ℝ)^n*Real.exp (-b*θ^2))
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplit :
      (∫ θ in -Real.pi..Real.pi,
        (39/20 : ℝ)^n + (2:ℝ)^n*Real.exp (-b*θ^2)) =
      (2*Real.pi)*(39/20 : ℝ)^n + (2:ℝ)^n *
        (∫ θ in -Real.pi..Real.pi, Real.exp (-b*θ^2)) := by
    rw [intervalIntegral.integral_add hCint hEint,
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul]
    ring_nf
  calc
    _ ≤ ∫ θ in -Real.pi..Real.pi,
      (39/20 : ℝ)^n + (2:ℝ)^n*Real.exp (-b*θ^2) := hmono
    _ = (2*Real.pi)*(39/20 : ℝ)^n + (2:ℝ)^n *
      (∫ θ in -Real.pi..Real.pi, Real.exp (-b*θ^2)) := hsplit
    _ ≤ (2*Real.pi)*(39/20 : ℝ)^n + (2:ℝ)^n *
      Real.sqrt (Real.pi / ((n:ℝ)*(8/5)/Real.pi^2)) := by
        dsimp [b] at hgauss ⊢
        gcongr

end SpringerLean

#print axioms SpringerLean.gaussian_principal_interval_le
#print axioms SpringerLean.affinePlatform_principal_integral_le
