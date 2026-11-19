import SpringerLean.Round714AngularPairedCandidates
import SpringerLean.Round716AngularIntegratedCircle
import SpringerLean.Round699LogarithmicTopContinuity
import SpringerLean.Round31PairAverage

open MeasureTheory Set Metric

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem angularRealCircle_re (x ρ θ : ℝ) :
    (circleMap (x : ℂ) ρ θ).re = x+ρ*Real.cos θ := by
  rw [show circleMap (x : ℂ) ρ θ = (x : ℂ)+circleMap 0 ρ θ from by simp [circleMap]]
  simp [Complex.add_re, circleMap_zero_re]

private theorem angularRealCircle_im (x ρ θ : ℝ) :
    (circleMap (x : ℂ) ρ θ).im = ρ*Real.sin θ := by
  rw [show circleMap (x : ℂ) ρ θ = (x : ℂ)+circleMap 0 ρ θ from by simp [circleMap]]
  simp [Complex.add_im, circleMap_zero_im]

/-- The actual angular star function satisfies a local circle submean.
ONE positive radius works for ALL smaller circles.  The maximizing set,
angular cut, contained interval, excluded margins, candidate sets and
Fubini integrability are all constructed inside the proof. -/
theorem logarithmicActualTopValue_local_circle_submean_coordinates
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ)
    (x h : ℝ) (hx : x < 0) (hh0 : 0 < h) (hhpi : h < Real.pi) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      logarithmicActualTopValue F c ((x : ℂ)+(h : ℂ)*Complex.I) ≤
        Real.circleAverage (logarithmicActualTopValue F c)
          ((x : ℂ)+(h : ℂ)*Complex.I) ρ := by
  obtain ⟨E, δ, hEm, hEb, hδ, hval, hpaired⟩ :=
    actualAngularTopValue_exists_uniform_paired_optimizer F hc c
      (Real.exp_pos x).le (Real.exp_lt_one_iff.mpr hx) hh0 hhpi
  let r₀ := min δ (min (-x) (min h (Real.pi-h)))
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    exact lt_min hδ (lt_min (neg_pos.mpr hx) (lt_min hh0 (sub_pos.mpr hhpi)))
  refine ⟨r₀, hr₀, ?_⟩
  intro ρ hρ hρr₀
  have hρδ : ρ < δ := hρr₀.trans_le (min_le_left _ _)
  have hρx : ρ < -x := hρr₀.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hρh : ρ < h := hρr₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hρpi : ρ < Real.pi-h := hρr₀.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Q : ℂ → ℝ := fun z => ∫ t in E,
    positiveLogActualProjection F c (z+(t : ℂ)*Complex.I)
  let B : ℂ → ℝ := fun z => logarithmicActualTopValue F c (z+(h : ℂ)*Complex.I)
  have hQci : CircleIntegrable Q (x : ℂ) ρ :=
    positiveLogActualProjection_setIntegral_circleIntegrable F hc c E hEm hEb
      x ρ hρ.le hρx
  have hshift (θ : ℝ) : circleMap (x : ℂ) ρ θ+(h : ℂ)*Complex.I =
      circleMap ((x : ℂ)+(h : ℂ)*Complex.I) ρ θ := by
    simp only [circleMap]
    ring
  have hBci : CircleIntegrable B (x : ℂ) ρ := by
    change IntervalIntegrable (fun θ : ℝ =>
      logarithmicActualTopValue F c (circleMap (x : ℂ) ρ θ+(h : ℂ)*Complex.I))
      volume 0 (2*Real.pi)
    simp_rw [hshift]
    exact logarithmicActualTopValue_circleIntegrable F hc c hρ.le
      (by simpa using hρx) (by simpa using hρh) (by simpa using hρpi)
  have hQpair := circleAverage_real_center_eq_angle_pair Q x ρ hQci
  have hBpair := circleAverage_real_center_eq_angle_pair B x ρ hBci
  have hQint := circleIntegrable_angle_pair Q x ρ hQci
  have hBint := circleIntegrable_angle_pair B x ρ hBci
  have hQangle (θ : ℝ) : Q (circleMap (x : ℂ) ρ θ) =
      ∫ t in E, (c*actualHarmonic F
        (circleMap 0 (Real.exp (x+ρ*Real.cos θ)) (t+ρ*Real.sin θ))).re := by
    apply integral_congr_ae
    filter_upwards [] with t
    have hs : circleMap (x : ℂ) ρ θ+(t : ℂ)*Complex.I =
        ((x+ρ*Real.cos θ : ℝ) : ℂ)+((t+ρ*Real.sin θ : ℝ) : ℂ)*Complex.I := by
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          angularRealCircle_re, angularRealCircle_im, mul_zero, zero_mul, mul_one,
          sub_zero, sub_self, add_zero, zero_add] <;> ring
    change positiveLogActualProjection F c (circleMap (x : ℂ) ρ θ+(t : ℂ)*Complex.I) = _
    rw [hs, positiveLogActualProjection_angle]
  have hBangle (θ : ℝ) : B (circleMap (x : ℂ) ρ θ) =
      actualAngularTopValue F c (Real.exp (x+ρ*Real.cos θ)) (h+ρ*Real.sin θ) := by
    simp [B, logarithmicActualTopValue, angularRealCircle_re, angularRealCircle_im, add_comm]
  have hmono : (∫ θ in (0 : ℝ)..Real.pi,
      Q (circleMap (x : ℂ) ρ θ)+Q (circleMap (x : ℂ) ρ (-θ))) ≤
      ∫ θ in (0 : ℝ)..Real.pi,
        B (circleMap (x : ℂ) ρ θ)+B (circleMap (x : ℂ) ρ (-θ)) := by
    apply intervalIntegral.integral_mono_on Real.pi_pos.le hQint hBint
    intro θ hθ
    have hε0 : 0 ≤ ρ*Real.sin θ := mul_nonneg hρ.le (Real.sin_nonneg_of_mem_Icc hθ)
    have hεδ : ρ*Real.sin θ < δ :=
      (mul_le_of_le_one_right hρ.le (Real.sin_le_one θ)).trans_lt hρδ
    have hr' : Real.exp (x+ρ*Real.cos θ) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hb := mul_le_of_le_one_right hρ.le (Real.cos_le_one θ)
      linarith
    have hp := hpaired (ρ*Real.sin θ) hε0 hεδ
      (Real.exp (x+ρ*Real.cos θ)) (Real.exp_pos _).le hr'
    have hQminus : Q (circleMap (x : ℂ) ρ (-θ)) =
        ∫ t in E, (c*actualHarmonic F
          (circleMap 0 (Real.exp (x+ρ*Real.cos θ)) (t-ρ*Real.sin θ))).re := by
      simpa only [Real.cos_neg, Real.sin_neg, mul_neg, sub_eq_add_neg] using hQangle (-θ)
    have hBminus : B (circleMap (x : ℂ) ρ (-θ)) =
        actualAngularTopValue F c (Real.exp (x+ρ*Real.cos θ)) (h-ρ*Real.sin θ) := by
      simpa only [Real.cos_neg, Real.sin_neg, mul_neg, sub_eq_add_neg] using hBangle (-θ)
    rw [hQangle θ, hQminus, hBangle θ, hBminus]
    linarith
  have hcenter : logarithmicActualTopValue F c ((x : ℂ)+(h : ℂ)*Complex.I) =
      ∫ t in E, positiveLogActualProjection F c ((x : ℂ)+(t : ℂ)*Complex.I) := by
    simp only [logarithmicActualTopValue, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, sub_self,
      add_zero, zero_add]
    rw [hval]
    apply integral_congr_ae
    filter_upwards [] with t
    exact (positiveLogActualProjection_angle F c x t).symm
  have hQmean := positiveLogActualProjection_setIntegral_circleAverage
    F hc c E hEm hEb x ρ hρ.le hρx
  have hBmean : Real.circleAverage B (x : ℂ) ρ =
      Real.circleAverage (logarithmicActualTopValue F c)
        ((x : ℂ)+(h : ℂ)*Complex.I) ρ := by
    rw [Real.circleAverage_def, Real.circleAverage_def]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact congrArg (logarithmicActualTopValue F c) (hshift θ)
  calc
    logarithmicActualTopValue F c ((x : ℂ)+(h : ℂ)*Complex.I) =
        Real.circleAverage Q (x : ℂ) ρ := hcenter.trans hQmean
    _ = (2*Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
        Q (circleMap (x : ℂ) ρ θ)+Q (circleMap (x : ℂ) ρ (-θ)) := hQpair
    _ ≤ (2*Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..Real.pi,
        B (circleMap (x : ℂ) ρ θ)+B (circleMap (x : ℂ) ρ (-θ)) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = Real.circleAverage B (x : ℂ) ρ := hBpair.symm
    _ = Real.circleAverage (logarithmicActualTopValue F c)
        ((x : ℂ)+(h : ℂ)*Complex.I) ρ := hBmean

theorem logarithmicActualTopValue_local_circle_submean
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c z : ℂ)
    (hx : z.re < 0) (hh0 : 0 < z.im) (hhpi : z.im < Real.pi) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      logarithmicActualTopValue F c z ≤
        Real.circleAverage (logarithmicActualTopValue F c) z ρ := by
  simpa only [Complex.re_add_im] using
    logarithmicActualTopValue_local_circle_submean_coordinates F hc c z.re z.im hx hh0 hhpi

end SpringerLean

#print axioms SpringerLean.logarithmicActualTopValue_local_circle_submean_coordinates
#print axioms SpringerLean.logarithmicActualTopValue_local_circle_submean
