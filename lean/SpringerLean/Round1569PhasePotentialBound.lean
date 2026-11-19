import SpringerLean.Round1568SelectedTwoUnitDiskGains

open MeasureTheory Set Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The zero-extension of the actual weighted phase potential.
Lean's real division sets the density to zero when `H=0`. -/
noncomputable def actualHarmonicPhasePotentialDensity
    (F : ℂ → ℂ) (k : ℕ) (β : ℂ) (z : ℂ) : ℝ :=
  (actualHarmonicPhaseField F k β z)^2 /
    ‖actualHarmonic F z‖^2

/-- The potential density has the expected removable-zero bound,
uniformly on the open disk. -/
theorem actualHarmonicPhasePotentialDensity_pointwise_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    0 ≤ actualHarmonicPhasePotentialDensity F k β z ∧
    actualHarmonicPhasePotentialDensity F k β z ≤
      (2:ℝ)^(2*k-2) := by
  let H : ℂ := actualHarmonic F z
  let U : ℝ := (β*H^k).im
  have hnorm : ‖H‖ ≤ 2 := by
    have hb := actualHarmonic_norm_le_two_norm F hc hz
    have hz0 := norm_nonneg z
    nlinarith
  have hUp : |U| ≤ ‖H‖^k := by
    calc
      |U| ≤ ‖β*H^k‖ := Complex.abs_im_le_norm _
      _ = ‖H‖^k := by rw [norm_mul,hβ,one_mul,norm_pow]
  have hpow : ‖H‖^(k-1) ≤ (2:ℝ)^(k-1) :=
    pow_le_pow_left₀ (norm_nonneg H) hnorm _
  have hUbound : |U| ≤ ‖H‖*(2:ℝ)^(k-1) := by
    have hcast : ‖H‖^k = ‖H‖*‖H‖^(k-1) := by
      conv_lhs => rw [show k=k-1+1 by omega,pow_succ]
      ring
    rw [hcast] at hUp
    exact hUp.trans (mul_le_mul_of_nonneg_left hpow (norm_nonneg H))
  have hnonneg : 0 ≤ actualHarmonicPhasePotentialDensity F k β z := by
    dsimp [actualHarmonicPhasePotentialDensity]
    positivity
  refine ⟨hnonneg,?_⟩
  by_cases hH0 : ‖H‖ = 0
  · have hzero : H = 0 := norm_eq_zero.mp hH0
    simp [actualHarmonicPhasePotentialDensity,actualHarmonicPhaseField,H,hzero]
  · have hHp : 0 < ‖H‖ := lt_of_le_of_ne (norm_nonneg H) (Ne.symm hH0)
    have hsq : U^2 ≤ (‖H‖*(2:ℝ)^(k-1))^2 := by
      have := (sq_le_sq₀ (abs_nonneg U)
        (mul_nonneg (norm_nonneg H) (by positivity))).mpr hUbound
      simpa only [sq_abs] using this
    have hdiv : U^2/‖H‖^2 ≤ ((2:ℝ)^(k-1))^2 := by
      apply (div_le_iff₀ (sq_pos_of_pos hHp)).2
      nlinarith [hsq]
    have hpow2 : ((2:ℝ)^(k-1))^2 = (2:ℝ)^(2*k-2) := by
      rw [←pow_mul]
      congr 1
      omega
    simpa only [actualHarmonicPhasePotentialDensity,
      actualHarmonicPhaseField,H,U,hpow2] using hdiv

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhasePotentialDensity_pointwise_le
