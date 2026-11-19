import SpringerLean.Round1566ActualPowerGainIntegrable

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The signed projected-power saving on a compact inner ball cannot
decrease when the outer radius tends to the open unit disk. -/
theorem actualHarmonic_positivePower_ball_gain_le_unitDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {b₀ : ℝ} (hb₀0 : 0 ≤ b₀) (hb₀1 : b₀ < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    (∫ z in ball (0:ℂ) b₀,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m) ≤
    ∫ z in ball (0:ℂ) 1,
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m := by
  let f : ℂ → ℝ := fun z =>
    (max (2*z.re) 0)^m-
      (max ((conj ξ*actualHarmonic F z).re) 0)^m
  have hf := actualHarmonic_positivePower_gain_integrableOn_unitDisk
    F hc ξ hξ m
  have hmono (b : ℝ) (hb : b₀ ≤ b) (hb1 : b < 1) :
      (∫ z in ball (0:ℂ) b₀, f z) ≤ ∫ z in ball (0:ℂ) b, f z :=
    actualHarmonic_positivePower_ball_gain_mono
      F hc ξ hξ hb₀0 hb hb1 hm
  exact unitDisk_integral_ge_of_innerBall_mono f hf hb₀1 hmono

/-- The actual harmonic filling's full open-unit-disk projected-power
gain exceeds `D^3/30` in the exact phase-budget normalization. -/
theorem actualHarmonic_positivePower_unitDisk_cubic_gain
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (ξ : ℂ) (hξ : ‖ξ‖ = 1)
    {h d : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hd : d=2-2*Real.sin h/h) (hd0 : 0 < d)
    (hcap : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ*w).re ≤ 2*Real.sin h/h)
    {m : ℕ} (hm : 1500 ≤ m) (hD : (m:ℝ)*d ≤ 3/20) :
    ((m:ℝ)*d)^3/30 <
      ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹*
      (∫ z in ball (0:ℂ) 1,
        (max (2*z.re) 0)^m-
          (max ((conj ξ*actualHarmonic F z).re) 0)^m) := by
  obtain ⟨b,hab,hb1,hgain⟩ :=
    actualHarmonic_positivePower_exists_interiorDisk_cubic_gain
      F hc ξ hξ hh0 hhpi hd hd0 hcap hm hD
  have ha0 : 0 ≤ 1-Real.sqrt d/16 := by
    have ha1 : 1-Real.sqrt d/16 ≤ 1 := by
      linarith [Real.sqrt_nonneg d]
    have hp := thinAnnulus_peak_parameter_bounds hm hd0 hD
      (le_refl _) ha1
    linarith [hp.2.2]
  have hb0 : 0 ≤ b := ha0.trans hab
  have hle := actualHarmonic_positivePower_ball_gain_le_unitDisk
    F hc ξ hξ hb0 hb1 (by omega : 1 ≤ m)
  have hball := setIntegral_congr_set
    (f := fun z : ℂ =>
      (max (2*z.re) 0)^m-
        (max ((conj ξ*actualHarmonic F z).re) 0)^m)
    (greenPolarRegion_zero_ae_ball b)
  rw [hball] at hgain
  have hN : 0 ≤ ((m:ℝ)*Real.sqrt (m:ℝ)/(2:ℝ)^m)*Real.pi⁻¹ := by
    positivity
  exact lt_of_lt_of_le hgain (mul_le_mul_of_nonneg_left hle hN)

end SpringerLean

#print axioms SpringerLean.actualHarmonic_positivePower_ball_gain_le_unitDisk
#print axioms SpringerLean.actualHarmonic_positivePower_unitDisk_cubic_gain
