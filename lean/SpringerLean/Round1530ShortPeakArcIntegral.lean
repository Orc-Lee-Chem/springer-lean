import SpringerLean.Round1529PowerQuadraticGap

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The exact one-dimensional mass of the squared loss on the short
comparison arc. -/
theorem shortPeakArc_square_integral {v : ℝ} (hv : 0 ≤ v) :
    (∫ θ in (0:ℝ)..Real.sqrt v, (v-θ^2)^2) =
      (8/15:ℝ)*v^2*Real.sqrt v := by
  let b := Real.sqrt v
  have hb : 0 ≤ b := Real.sqrt_nonneg v
  have hb2 : b^2 = v := Real.sq_sqrt hv
  have hpoly : ∀ θ : ℝ, (v-θ^2)^2 = v^2-2*v*θ^2+θ^4 := by
    intro θ
    ring
  simp_rw [hpoly]
  have h2 : (∫ θ in (0:ℝ)..b, θ^2) = b^3/3 :=
    (coarseArc_polynomial_moments b).1
  have h4 : (∫ θ in (0:ℝ)..b, θ^4) = b^5/5 :=
    (coarseArc_polynomial_moments b).2
  have hi : (∫ θ in (0:ℝ)..b, v^2-2*v*θ^2+θ^4) =
      v^2*b-2*v*(b^3/3)+b^5/5 := by
    have hA : IntervalIntegrable (fun θ : ℝ => v^2-2*v*θ^2) volume 0 b := by
      apply Continuous.intervalIntegrable; fun_prop
    have hB : IntervalIntegrable (fun θ : ℝ => θ^4) volume 0 b := by
      apply Continuous.intervalIntegrable; fun_prop
    have hC : IntervalIntegrable (fun _ : ℝ => v^2) volume 0 b := by
      apply Continuous.intervalIntegrable; fun_prop
    have hD : IntervalIntegrable (fun θ : ℝ => 2*v*θ^2) volume 0 b := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_add hA hB,
      intervalIntegral.integral_sub hC hD,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,h2,h4]
    simp [smul_eq_mul]
    ring
  change (∫ θ in (0:ℝ)..b, v^2-2*v*θ^2+θ^4) = _
  rw [hi]
  rw [←hb2]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hb]
  ring

end SpringerLean

#print axioms SpringerLean.shortPeakArc_square_integral
