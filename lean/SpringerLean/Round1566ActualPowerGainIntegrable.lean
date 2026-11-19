import SpringerLean.Round1565ActualBallGainMonotone

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The signed difference of projected positive powers is genuinely
integrable on the open unit disk. Both powers lie in `[0,2^m]`. -/
theorem actualHarmonic_positivePower_gain_integrableOn_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1) (m : ℕ) :
    IntegrableOn (fun z : ℂ =>
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m)
      (ball (0:ℂ) 1) := by
  let D : Set ℂ := ball 0 1
  let Y : ℂ → ℝ := fun z => (max (2*z.re) 0)^m
  let X : ℂ → ℝ := fun z =>
    (max ((conj ξ*actualHarmonic F z).re) 0)^m
  let f : ℂ → ℝ := fun z => Y z-X z
  have hH := actualHarmonic_continuousOn_unitBall F hc
  have hX : ContinuousOn X D := by
    have hproj : ContinuousOn
        (fun z : ℂ => (conj ξ*actualHarmonic F z).re) D :=
      Complex.continuous_re.comp_continuousOn
        (continuousOn_const.mul hH)
    exact (continuous_max.comp_continuousOn
      (hproj.prodMk continuousOn_const)).pow m
  have hY : ContinuousOn Y D := by dsimp [Y]; fun_prop
  have hf : ContinuousOn f D := hY.sub hX
  have hbound (z : ℂ) (hz : z ∈ D) : ‖f z‖ ≤ (2:ℝ)^m := by
    have hn : ‖z‖ < 1 := by simpa only [D,mem_ball,dist_zero_right] using hz
    have hHbound := actualHarmonic_norm_le_two_norm F hc hn
    have hmult : ‖conj ξ*actualHarmonic F z‖ =
        ‖actualHarmonic F z‖ := by
      rw [norm_mul,Complex.norm_conj,hξ,one_mul]
    have hReX := Complex.abs_re_le_norm (conj ξ*actualHarmonic F z)
    have hReY := Complex.abs_re_le_norm z
    have hxmax : max ((conj ξ*actualHarmonic F z).re) 0 ≤ 2 := by
      rw [max_le_iff]
      constructor
      · have hp := (abs_le.mp hReX).2
        rw [hmult] at hp
        nlinarith
      · norm_num
    have hymax : max (2*z.re) 0 ≤ 2 := by
      rw [max_le_iff]
      constructor
      · have hp := (abs_le.mp hReY).2
        nlinarith
      · norm_num
    have hxp : X z ≤ (2:ℝ)^m :=
      pow_le_pow_left₀ (by positivity) hxmax m
    have hyp : Y z ≤ (2:ℝ)^m :=
      pow_le_pow_left₀ (by positivity) hymax m
    have hx0 : 0 ≤ X z := by dsimp [X]; positivity
    have hy0 : 0 ≤ Y z := by dsimp [Y]; positivity
    change ‖Y z-X z‖ ≤ (2:ℝ)^m
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  change IntegrableOn f D
  exact integrableOn_unitDisk_of_continuousOn_bound f hf ((2:ℝ)^m) hbound

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_gain_integrableOn_unitDisk
