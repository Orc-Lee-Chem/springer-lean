import SpringerLean.Round1793ActualBothAlignedPointwise
import SpringerLean.Round1775ComparisonPositiveCatalan

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 600000

theorem alignedPhaseTest_actual_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (a : ℝ) (v : ℂ) (hv : ‖v‖=1) :
    IntegrableOn (fun z => alignedPhaseTest k a v (actualHarmonic F z)) (ball (0 : ℂ) 1) := by
  let ψ : ℝ → ℝ := fun x =>
    twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12) x/(2 : ℝ)^(2*k-2)
  have hψ : Continuous ψ := by
    change Continuous (fun x : ℝ =>
      max ((max x 0)^(2*k-12+10))
        ((2*(1-a/((2*k-2 : ℕ) : ℝ)))^8*(max x 0)^(2*k-12+2))/(2 : ℝ)^(2*k-2))
    fun_prop
  exact actualHarmonic_projection_test_integrableOn F hc v hv ψ hψ

theorem normalized_unitDisk_integral_const (c : ℝ) :
    Real.pi⁻¹*(∫ _z in ball (0 : ℂ) 1, c)=c := by
  have hmass : Real.pi⁻¹*(∫ _z in ball (0 : ℂ) 1, (1 : ℝ))=1 := by
    apply Complex.ofReal_injective
    push_cast
    rw [←integral_complex_ofReal]
    exact comparisonDisk_mass
  have hfun : (fun _z : ℂ => c)=(fun _z : ℂ => c*(1 : ℝ)) := by funext; ring
  rw [hfun, integral_const_mul]
  calc
    _ = c*(Real.pi⁻¹*(∫ _z in ball (0 : ℂ) 1, (1 : ℝ))) := by ring
    _ = c := by rw [hmass, mul_one]

theorem actualSignedPhaseIntegral_two_aligned_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (hδ₁ : |(k : ℝ)*ends.θ₁| ≤ Real.pi/3)
    (hδ₂ : |(k : ℝ)*ends.θ₂| ≤ Real.pi/3)
    (a₁ a₂ : ℝ) (ha₁ : 6 ≤ a₁) (ha₂ : 6 ≤ a₂)
    (hay₁ : a₁*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₁) ≤ 3)
    (hay₂ : a₂*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth ends.P₂) ≤ 3) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) ≤
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, alignedPhaseTest k a₁ ends.v₁ (actualHarmonic F z))+
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, alignedPhaseTest k a₂ ends.v₂ (actualHarmonic F z))+
        (23/25 : ℝ)^(2*k-2) := by
  have hS := actualSignedPhaseDensity_integrableOn F hc (by omega : 1 ≤ k) beta hbeta
  have h₁ := alignedPhaseTest_actual_integrableOn F hc k a₁ ends.v₁ ends.unit₁
  have h₂ := alignedPhaseTest_actual_integrableOn F hc k a₂ ends.v₂ ends.unit₂
  have hC : IntegrableOn (fun _z : ℂ => (23/25 : ℝ)^(2*k-2)) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ continuousOn_const
      ‖(23/25 : ℝ)^(2*k-2)‖ (fun _ _ => le_refl _)
  have hpoint : (fun z => actualSignedPhaseDensity F k beta z) ≤ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      (fun z => alignedPhaseTest k a₁ ends.v₁ (actualHarmonic F z)+
        alignedPhaseTest k a₂ ends.v₂ (actualHarmonic F z)+(23/25 : ℝ)^(2*k-2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
    exact actualSignedPhaseDensity_two_aligned_global F hc k hk beta ends hδ₁ hδ₂
      a₁ a₂ ha₁ ha₂ hay₁ hay₂ z (by simpa only [mem_ball, dist_zero_right] using hz)
  have hi := integral_mono_ae hS ((h₁.add h₂).add hC) hpoint
  have hn := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ Real.pi⁻¹)
  have hsum := integral_add (h₁.add h₂) hC
  simp only [Pi.add_apply] at hn hsum
  rw [hsum, integral_add h₁ h₂] at hn
  have hconst := normalized_unitDisk_integral_const ((23/25 : ℝ)^(2*k-2))
  nlinarith

end
end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_two_aligned_le
