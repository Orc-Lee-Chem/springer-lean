import SpringerLean.Round1535PoissonHalfMass

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The antiderivative needed only on arcs separated from the kernel
singularity at zero. -/
theorem cotangentTail_hasDerivAt
    {θ : ℝ} (hθ0 : 0 < θ) (hθpi : θ ≤ Real.pi) :
    HasDerivAt (fun t : ℝ => -2*Real.cos (t/2)/Real.sin (t/2))
      (1/Real.sin (θ/2)^2) θ := by
  have hθhalf : 0 < θ/2 ∧ θ/2 < Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hs : Real.sin (θ/2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθhalf.1 hθhalf.2)
  have harg : HasDerivAt (fun t : ℝ => t/2) (1/2:ℝ) θ := by
    simpa [id_eq,div_eq_mul_inv] using (hasDerivAt_id θ).div_const 2
  have hc := (Real.hasDerivAt_cos (θ/2)).comp θ harg
  have hsder := (Real.hasDerivAt_sin (θ/2)).comp θ harg
  have hdiv := (hc.const_mul (-2)).div hsder hs
  convert hdiv using 1
  · funext t; dsimp
  · dsimp
    have htrig := Real.sin_sq_add_cos_sq (θ/2)
    field_simp
    nlinarith [htrig]

/-- Integrating the reciprocal squared sine gives twice the endpoint
cotangent; the upper endpoint is π, where its cotangent is zero. -/
theorem reciprocalSineSquare_halfAngle_integral
    {h : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi) :
    (∫ θ in h..Real.pi, 1/Real.sin (θ/2)^2) =
      2*Real.cos (h/2)/Real.sin (h/2) := by
  let f : ℝ → ℝ := fun θ => -2*Real.cos (θ/2)/Real.sin (θ/2)
  have hsin : ∀ θ ∈ Icc h Real.pi, Real.sin (θ/2) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [hθ.1]) (by linarith [hθ.2,Real.pi_pos]))
  have hcont : ContinuousOn (fun θ : ℝ => 1/Real.sin (θ/2)^2)
      (Icc h Real.pi) := by
    apply ContinuousOn.div continuousOn_const
    · fun_prop
    · intro θ hθ
      exact pow_ne_zero _ (hsin θ hθ)
  have hInt : IntervalIntegrable (fun θ : ℝ => 1/Real.sin (θ/2)^2)
      volume h Real.pi :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hFTC : (∫ θ in h..Real.pi, 1/Real.sin (θ/2)^2) =
      f Real.pi-f h := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro θ hθ
      have hθ' : θ ∈ Icc h Real.pi := by
        simpa [uIcc_of_le hhpi.le] using hθ
      exact cotangentTail_hasDerivAt
        (by linarith [hθ'.1]) hθ'.2
    · exact hInt
  rw [hFTC]
  dsimp [f]
  simp [Real.sin_pi_div_two,Real.cos_pi_div_two]
  ring

end SpringerLean

#print axioms SpringerLean.cotangentTail_hasDerivAt
#print axioms SpringerLean.reciprocalSineSquare_halfAngle_integral
