import SpringerLean.Round1810ActualEndpointPhaseEnvelope

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 700000

theorem endpointPhaseTest_actual_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (P v : ℂ) (δ : ℝ) (hv : ‖v‖=1) (hP : 0 < ‖P‖) :
    IntegrableOn (fun z => endpointPhaseTest k P v δ (actualHarmonic F z))
      (ball (0 : ℂ) 1) := by
  unfold endpointPhaseTest
  split_ifs
  · exact alignedPhaseTest_actual_integrableOn F hc k _ v hv
  · have haxis : ‖P/(‖P‖ : ℂ)‖=1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP, div_self hP.ne']
    exact actualHarmonic_projection_test_integrableOn F hc _ haxis
      (fun x : ℝ => trueAxisMomentRatioLambda ((2*k-2 : ℕ) : ℝ)*(max (x/2) 0)^(2*k-10))
      (by fun_prop)

theorem ActualCandidatePhaseEndpoints.radius_pos
    (F : ℂ → ℂ) (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    0 < ‖ends.P₁‖ ∧ 0 < ‖ends.P₂‖ := by
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  constructor
  · nlinarith [ends.scaled_deficit₁, mul_le_mul_of_nonneg_right hn ends.deficit_pos₁.le]
  · nlinarith [ends.scaled_deficit₂, mul_le_mul_of_nonneg_right hn ends.deficit_pos₂.le]

/-- The actual disk comparison now covers every recorded phase.
The central allowance is counted once, independently of the two tests. -/
theorem actualSignedPhaseIntegral_endpointTests_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) ≤
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
        endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z))+
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z))+
      (23/25 : ℝ)^(2*k-2) := by
  have hS := actualSignedPhaseDensity_integrableOn F hc (by omega : 1 ≤ k) beta hbeta
  obtain ⟨hP₁,hP₂⟩ := ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends
  have h₁ := endpointPhaseTest_actual_integrableOn F hc k ends.P₁ ends.v₁ ends.θ₁ ends.unit₁ hP₁
  have h₂ := endpointPhaseTest_actual_integrableOn F hc k ends.P₂ ends.v₂ ends.θ₂ ends.unit₂ hP₂
  have hC : IntegrableOn (fun _z : ℂ => (23/25 : ℝ)^(2*k-2)) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ continuousOn_const
      ‖(23/25 : ℝ)^(2*k-2)‖ (fun _ _ => le_refl _)
  have hpoint : (fun z => actualSignedPhaseDensity F k beta z) ≤ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      (fun z => endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)+
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)+(23/25 : ℝ)^(2*k-2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
    exact actualSignedPhaseDensity_endpointTests_global F hc k hk beta ends z
      (by simpa only [mem_ball,dist_zero_right] using hz)
  have hi := integral_mono_ae hS ((h₁.add h₂).add hC) hpoint
  have hn := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ Real.pi⁻¹)
  have hsum := integral_add (h₁.add h₂) hC
  simp only [Pi.add_apply] at hn hsum
  rw [hsum, integral_add h₁ h₂] at hn
  have hconst := normalized_unitDisk_integral_const ((23/25 : ℝ)^(2*k-2))
  nlinarith

end
end SpringerLean

#print axioms SpringerLean.actualSignedPhaseIntegral_endpointTests_le
