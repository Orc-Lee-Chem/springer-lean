import SpringerLean.Round1380EvenCircleIntegral
import SpringerLean.Round1374HalfCosMoments

open MeasureTheory

namespace SpringerLean

theorem coarseAngleDeficit_le_sin_sq
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    coarseAngleDeficit v ≤ (80/79 : ℝ) * Real.sin v ^ 2 := by
  have he := coarseAngleDeficit_range hv0 hvβ
  have hcoslo : (39/40 : ℝ) ≤ Real.cos v := by
    have hβπ : coarseAngleBeta ≤ Real.pi := by
      linarith [coarseAngleBeta_range.2, Real.pi_pos]
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hv0 hβπ hvβ
    change Real.cos (Real.arccos (39/40 : ℝ)) ≤ Real.cos v at hc
    rw [Real.cos_arccos (by norm_num) (by norm_num)] at hc
    exact hc
  have hprod : 0 ≤ coarseAngleDeficit v * (Real.cos v - 39/40) :=
    mul_nonneg he.1 (by linarith)
  have htrig := Real.sin_sq_add_cos_sq v
  unfold coarseAngleDeficit at *
  nlinarith

theorem coarseAngle_active_cost_le (n : ℕ) :
    (∫ θ in (0:ℝ)..coarseAngleAlpha,
      coarseInverseRadius (2*Real.cos θ)^n) ≤
    (2:ℝ)^n * halfCosMoment n *
      (1+800/(79*(((n+2:ℕ):ℝ)))) := by
  let q : ℝ → ℝ := fun v => (2*Real.cos v)^n
  let g : ℝ → ℝ := fun v => q v * (1+(800/79 : ℝ)*Real.sin v^2)
  have hβ0 := coarseAngleBeta_range.1
  have hβhalf := coarseAngleBeta_range.2
  have hqcont : Continuous q := by dsimp [q]; fun_prop
  have hgcont : Continuous g := by dsimp [g,q]; fun_prop
  have hderivcont := coarseAnglePhi_deriv_continuousOn
  have hleft : IntervalIntegrable
      (fun v : ℝ => q v * deriv coarseAnglePhi v)
      volume 0 coarseAngleBeta := by
    apply ContinuousOn.intervalIntegrable_of_Icc hβ0
    exact hqcont.continuousOn.mul hderivcont
  have hright : IntervalIntegrable g volume 0 coarseAngleBeta :=
    hgcont.intervalIntegrable _ _
  have hfirst :
      (∫ θ in (0:ℝ)..coarseAngleAlpha,
        coarseInverseRadius (2*Real.cos θ)^n) ≤
      ∫ v in (0:ℝ)..coarseAngleBeta, g v := by
    rw [coarseAngle_active_integral_substitution]
    apply intervalIntegral.integral_mono_on_of_le_Ioo hβ0 hleft hright
    intro v hv
    have hvcos : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hv.1, Real.pi_pos], hv.2.le.trans hβhalf⟩
    have hq : 0 ≤ q v := pow_nonneg (mul_nonneg (by norm_num) hvcos) _
    have hderiv := (coarseAnglePhi_deriv_bounds hv.1 hv.2).2
    have he := coarseAngleDeficit_le_sin_sq hv.1.le hv.2.le
    dsimp [g]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hq
  have hsecond :
      (∫ v in (0:ℝ)..coarseAngleBeta, g v) ≤
      ∫ v in (0:ℝ)..Real.pi/2, g v := by
    apply intervalIntegral.integral_mono_interval le_rfl hβ0 hβhalf
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hcos : 0 ≤ Real.cos v := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hv.1, Real.pi_pos],hv.2⟩
      dsimp [g,q]
      positivity
    · exact hgcont.intervalIntegrable _ _
  have hfull :
      (∫ v in (0:ℝ)..Real.pi/2, g v) =
      (2:ℝ)^n * halfCosMoment n *
        (1+800/(79*(((n+2:ℕ):ℝ)))) := by
    dsimp [g,q]
    have hpoint (v : ℝ) :
        (2*Real.cos v)^n * (1+(800/79 : ℝ)*Real.sin v^2) =
          (2:ℝ)^n*Real.cos v^n +
            ((800/79:ℝ)*(2:ℝ)^n)*(Real.cos v^n*Real.sin v^2) := by
      rw [mul_pow]
      ring
    simp_rw [hpoint]
    have hInt₁ : IntervalIntegrable
        (fun v : ℝ => (2:ℝ)^n*Real.cos v^n) volume 0 (Real.pi/2) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hInt₂ : IntervalIntegrable
        (fun v : ℝ => ((800/79:ℝ)*(2:ℝ)^n)*
          (Real.cos v^n*Real.sin v^2)) volume 0 (Real.pi/2) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_add hInt₁ hInt₂]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [halfCosMoment_sin_sq]
    unfold halfCosMoment
    ring
  exact hfirst.trans (hsecond.trans_eq hfull)

end SpringerLean
