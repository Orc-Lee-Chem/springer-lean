import SpringerLean.Round1537CotangentBound

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 320000

/-- On the complementary half arc, remove the positive `(1-r)^2`
term from the Poisson denominator. -/
theorem centeredPoisson_tail_pointwise
    {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hθ0 : 0 < θ) (hθpi : θ ≤ Real.pi) :
    poissonKernel 0 (r:ℂ) (circleMap 0 1 θ) ≤
      (1-r^2)/(4*r*Real.sin (θ/2)^2) := by
  have hs : 0 < Real.sin (θ/2) :=
    Real.sin_pos_of_pos_of_lt_pi
      (by linarith) (by linarith [Real.pi_pos])
  have hcos : Real.cos θ=1-2*Real.sin (θ/2)^2 := by
    have hc := Real.cos_two_mul (θ/2)
    have hangle : 2*(θ/2)=θ := by ring
    rw [hangle] at hc
    have ht := Real.sin_sq_add_cos_sq (θ/2)
    nlinarith
  have hden : 1+r^2-2*r*Real.cos θ =
      (1-r)^2+4*r*Real.sin (θ/2)^2 := by
    rw [hcos]
    ring
  have hbase : 0 < 4*r*Real.sin (θ/2)^2 := by positivity
  have hden0 : 0 < 1+r^2-2*r*Real.cos θ := by
    rw [hden]
    nlinarith [sq_nonneg (1-r)]
  have hnum : 0 ≤ 1-r^2 := by nlinarith
  rw [poissonKernel_centered_cosine_formula hr0.le hr1]
  apply (div_le_div_iff₀ hden0 hbase).2
  rw [hden]
  nlinarith [mul_nonneg hnum (sq_nonneg (1-r))]

end SpringerLean

#print axioms SpringerLean.centeredPoisson_tail_pointwise
