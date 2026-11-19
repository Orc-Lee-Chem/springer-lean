import SpringerLean.Round1835ActualAntipodalPointwise

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 1300000

theorem actualDirectionalPowerSaving_integral_identity
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (m : ℕ) (v : ℂ) (hv : ‖v‖=1) :
    ((m : ℝ)*Real.sqrt (m : ℝ))*(comparisonPositiveDiskMoment m-
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
        (max ((conj v*actualHarmonic F z).re) 0)^m/(2 : ℝ)^m))=
      actualDirectionalPowerSaving F m v := by
  have hA := actualHarmonic_projection_test_integrableOn F hc v hv
    (fun x : ℝ => (max x 0)^m) (by fun_prop)
  have hR := comparisonDisk_test_integrableOn (fun x : ℝ => (max x 0)^m) (by fun_prop)
  have hscale (x : ℝ) : (max (2*x) 0)^m/(2 : ℝ)^m=(max x 0)^m := by
    have hm : max (2*x) 0=2*max x 0 := by
      rw [mul_max_of_nonneg x 0 (by norm_num : (0 : ℝ) ≤ 2),mul_zero]
    rw [hm,mul_pow]
    field_simp
  have href : Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^m)/(2 : ℝ)^m=
      comparisonPositiveDiskMoment m := by
    rw [show Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^m)/(2 : ℝ)^m=
      Real.pi⁻¹*((∫ z in ball (0 : ℂ) 1, (max (2*z.re) 0)^m)/(2 : ℝ)^m) by ring,
      ←integral_div]
    unfold comparisonPositiveDiskMoment
    exact congrArg (fun x : ℝ => Real.pi⁻¹*x) (integral_congr_ae (Filter.Eventually.of_forall (fun z => hscale z.re)))
  unfold actualDirectionalPowerSaving
  rw [integral_sub hR hA,integral_div,←href]
  ring

theorem antipodalPhaseTest_actual_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (v : ℂ) (hv : ‖v‖=1) :
    IntegrableOn (fun z => antipodalPhaseTest k v (actualHarmonic F z)) (ball (0 : ℂ) 1) := by
  have h₁ := actualHarmonic_projection_test_integrableOn F hc v hv
    (fun x : ℝ => (max x 0)^(2*k-2)/(2 : ℝ)^(2*k-2)) (by fun_prop)
  have h₂ := actualHarmonic_projection_test_integrableOn F hc (-v) (by simpa only [norm_neg] using hv)
    (fun x : ℝ => (max x 0)^(2*k-2)/(2 : ℝ)^(2*k-2)) (by fun_prop)
  exact h₁.add h₂

/-- Both real antipodal gains are retained at the SAME first-endpoint
deficit. Only the explicit vanishing central scalar remains. -/
theorem actualSignedPhaseIntegral_antipodal_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let d := 2-‖ends.P₁‖
    let E := d*Real.log (2/d)
    m*Real.sqrt m*(Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
      actualSignedPhaseDensity F k beta z)-2*comparisonPositiveDiskMoment (2*k-2)) <
      m*Real.sqrt m*(3*(k : ℝ)*Real.sqrt E)^(2*k-2)-(m*d)^3/15 := by
  let E := (2-‖ends.P₁‖)*Real.log (2/(2-‖ends.P₁‖))
  let C := (3*(k : ℝ)*Real.sqrt E)^(2*k-2)
  have hS := actualSignedPhaseDensity_integrableOn F hc (by omega : 1 ≤ k) beta hbeta
  have hA := antipodalPhaseTest_actual_integrableOn F hc k ends.v₁ ends.unit₁
  have hC : IntegrableOn (fun _z : ℂ => C) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ continuousOn_const ‖C‖ (fun _ _ => le_refl _)
  have hpoint : (fun z => actualSignedPhaseDensity F k beta z) ≤ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      (fun z => antipodalPhaseTest k ends.v₁ (actualHarmonic F z)+C) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
    exact actualSignedPhaseDensity_antipodal_global F hc k hk beta ends z
      (by simpa only [mem_ball,dist_zero_right] using hz)
  have hi := integral_mono_ae hS (hA.add hC) hpoint
  have hn := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ Real.pi⁻¹)
  have hsum := integral_add hA hC
  simp only [Pi.add_apply] at hn hsum
  rw [hsum] at hn
  have hconst := normalized_unitDisk_integral_const C
  have h₁ := actualHarmonic_projection_test_integrableOn F hc ends.v₁ ends.unit₁
    (fun x : ℝ => (max x 0)^(2*k-2)/(2 : ℝ)^(2*k-2)) (by fun_prop)
  have h₂ := actualHarmonic_projection_test_integrableOn F hc (-ends.v₁) (by simpa only [norm_neg] using ends.unit₁)
    (fun x : ℝ => (max x 0)^(2*k-2)/(2 : ℝ)^(2*k-2)) (by fun_prop)
  have htestsum := integral_add h₁ h₂
  unfold antipodalPhaseTest at hn
  rw [htestsum] at hn
  have hs₁ := actualDirectionalPowerSaving_integral_identity F hc (2*k-2) ends.v₁ ends.unit₁
  have hs₂ := actualDirectionalPowerSaving_integral_identity F hc (2*k-2) (-ends.v₁)
    (by simpa only [norm_neg] using ends.unit₁)
  have hgain := ActualCandidatePhaseEndpoints.first_all_direction_gains F hc k hk beta ends
  have hg₁ := hgain ends.v₁ ends.unit₁
  have hg₂ := hgain (-ends.v₁) (by simpa only [norm_neg] using ends.unit₁)
  rw [←hs₁] at hg₁
  rw [←hs₂] at hg₂
  have hcost : Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) ≤
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max ((conj ends.v₁*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2))+
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max ((conj (-ends.v₁)*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2))+C := by
    nlinarith [hn,hconst]
  have hh := mul_le_mul_of_nonneg_left hcost
    (show 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) by positivity)
  dsimp only
  dsimp [C,E] at hconst hh
  nlinarith [hh,hg₁,hg₂]

end
end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_antipodal_budget
