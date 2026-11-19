import SpringerLean.Round1768TwoPowerConvexRetention
import SpringerLean.Round1766SelectedTiltedDiskSavings
import SpringerLean.Round749ActualDiskConvex

open MeasureTheory Metric Set
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 600000

/-- Every continuous finite test is integrable on the actual projected
disk. No radial boundary trace or boundary smoothness is required. -/
theorem actualHarmonic_projection_test_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ℂ) (hv : ‖v‖=1) (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    IntegrableOn (fun z => ψ ((conj v*actualHarmonic F z).re)) (ball (0 : ℂ) 1) := by
  have hcont : ContinuousOn (fun z => (conj v*actualHarmonic F z).re)
      (ball (0 : ℂ) 1) := Complex.continuous_re.comp_continuousOn
    (continuousOn_const.mul (actualHarmonic_continuousOn_unitBall F hc))
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).image hψ).isBounded.exists_norm_le
  apply integrableOn_unitDisk_of_continuousOn_bound _ (hψ.comp_continuousOn hcont) C
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hn := actualHarmonic_norm_le_two_norm F hc hz'
  have hp := Complex.abs_re_le_norm (conj v*actualHarmonic F z)
  rw [norm_mul, Complex.norm_conj, hv, one_mul] at hp
  have hr : (conj v*actualHarmonic F z).re ∈ Icc (-2 : ℝ) 2 := by
    have hab := abs_le.mp hp
    constructor <;> nlinarith
  exact hC _ ⟨_,hr,rfl⟩

theorem comparisonDisk_test_integrableOn (ψ : ℝ → ℝ) (hψ : Continuous ψ) :
    IntegrableOn (fun z : ℂ => ψ (2*z.re)) (ball (0 : ℂ) 1) := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).image hψ).isBounded.exists_norm_le
  apply integrableOn_unitDisk_of_continuousOn_bound _ (by fun_prop) C
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hab := abs_le.mp (Complex.abs_re_le_norm z)
  have hr : 2*z.re ∈ Icc (-2 : ℝ) 2 := by constructor <;> nlinarith
  exact hC _ ⟨_,hr,rfl⟩

def actualTwoPowerSaving (F : ℂ → ℂ) (j : ℕ) (R : ℝ) (v : ℂ) : ℝ :=
  (((j+10 : ℕ) : ℝ)*Real.sqrt ((j+10 : ℕ) : ℝ)/(2 : ℝ)^(j+10))*Real.pi⁻¹*
    (∫ z in ball (0 : ℂ) 1, twoPowerPhaseTest R j (2*z.re)-
      twoPowerPhaseTest R j ((conj v*actualHarmonic F z).re))

/-- Subtract the retained positive power BEFORE applying convex order.
This preserves the same directional saving, including its exact disk
area and m^(3/2)/2^m normalizations. -/
theorem actualHarmonic_twoPower_retains_directional_saving
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ℂ) (hv : ‖v‖=1) {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    phasePowerRetention j*actualDirectionalPowerSaving F (j+10) v ≤
      actualTwoPowerSaving F j R v := by
  let κ := phasePowerRetention j
  let g := twoPowerPhaseTest R j
  let p : ℝ → ℝ := fun x => (max x 0)^(j+10)
  have hg : Continuous g := by
    change Continuous (fun x : ℝ => max ((max x 0)^(j+10)) (R^8*(max x 0)^(j+2)))
    fun_prop
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hga := actualHarmonic_projection_test_integrableOn F hc v hv g hg
  have hpa := actualHarmonic_projection_test_integrableOn F hc v hv p hp
  have hgm := comparisonDisk_test_integrableOn g hg
  have hpm := comparisonDisk_test_integrableOn p hp
  have hle := actualHarmonic_disk_convex_le F hc v hv
    (fun x => g x-κ*p x) (twoPowerPhaseTest_sub_power_convexOn hR j)
  rw [integral_sub hga (hpa.const_mul κ), integral_sub hgm (hpm.const_mul κ),
    integral_const_mul, integral_const_mul] at hle
  have hN : 0 ≤ ((j+10 : ℕ) : ℝ)*Real.sqrt ((j+10 : ℕ) : ℝ)/(2 : ℝ)^(j+10) := by positivity
  have hh := mul_le_mul_of_nonneg_left hle hN
  unfold actualDirectionalPowerSaving actualTwoPowerSaving
  rw [integral_sub hgm hga, integral_sub hpm hpa]
  change κ*(_*Real.pi⁻¹*(_-_)) ≤ _*Real.pi⁻¹*(_-_)
  dsimp [g, p] at hh
  nlinarith [hh]

/-- Any strict cubic gain in this direction survives in the two-power
test with factor kappa; this is an actual-F statement. -/
theorem actualHarmonic_twoPower_cubic_gain_of_directional
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (v : ℂ) (hv : ‖v‖=1) {R D : ℝ} (hR : 0 ≤ R) (j : ℕ)
    (hgain : D^3/30 < actualDirectionalPowerSaving F (j+10) v) :
    phasePowerRetention j*D^3/30 < actualTwoPowerSaving F j R v := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hκ : 0 < phasePowerRetention j := by unfold phasePowerRetention; positivity
  have hle := actualHarmonic_twoPower_retains_directional_saving F hc v hv hR j
  have hh := mul_lt_mul_of_pos_left hgain hκ
  nlinarith

end
end SpringerLean

#print axioms SpringerLean.actualHarmonic_twoPower_retains_directional_saving
#print axioms SpringerLean.actualHarmonic_twoPower_cubic_gain_of_directional
