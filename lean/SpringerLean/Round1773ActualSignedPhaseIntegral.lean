import SpringerLean.Round1763ActualSignedPhaseBound

open MeasureTheory Metric

namespace SpringerLean
noncomputable section

/-- The phase comparison's signed density, with removable zeros and
the exact division by 2^m. This definition uses no argument function. -/
def actualSignedPhaseDensity (F : ℂ → ℂ) (k : ℕ) (beta z : ℂ) : ℝ :=
  (‖actualHarmonic F z‖^(2*k-2)-
    (8/25 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z)/(2 : ℝ)^(2*k-2)

theorem actualOmittedMoment_nonneg (F : ℂ → ℂ) (m : ℕ) :
    0 ≤ actualOmittedMoment F m := by
  unfold actualOmittedMoment
  exact mul_nonneg (by positivity) (integral_nonneg (fun _ => by positivity))

theorem actualSignedPhaseDensity_integrableOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1) :
    IntegrableOn (actualSignedPhaseDensity F k beta) (ball (0 : ℂ) 1) := by
  have hM := (actualHarmonic_weighted_integrableOn F hc (2*k-2)).1
  have hX := actualHarmonicPhasePotentialDensity_integrableOn_unitDisk F hc hk beta hbeta
  exact (hM.sub (hX.const_mul (8/25 : ℝ))).div_const _

theorem actualSignedPhaseDensity_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {k : ℕ} (hk : 1 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) =
      (actualHarmonicMoment F (2*k-2)-
        (8/25 : ℝ)*actualHarmonicPhasePotential F k beta)/(2 : ℝ)^(2*k-2) := by
  have hM := (actualHarmonic_weighted_integrableOn F hc (2*k-2)).1
  have hX := actualHarmonicPhasePotentialDensity_integrableOn_unitDisk F hc hk beta hbeta
  unfold actualSignedPhaseDensity actualHarmonicMoment actualHarmonicPhasePotential
  rw [integral_div, integral_sub hM (hX.const_mul _), integral_const_mul]
  ring

/-- The actual signed integral criterion used by the remaining phase
comparison. No energy premise remains, and equality candidates count. -/
theorem exteriorInverseCoeff_candidate_exists_signed_phase_integral
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ beta : ℂ, ‖beta‖=1 ∧
      (catalan (k-1) : ℝ)/(2 : ℝ)^(2*k-2) ≤
        Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, actualSignedPhaseDensity F k beta z) := by
  obtain ⟨beta, hbeta, hs⟩ := exteriorInverseCoeff_candidate_exists_signed_phase_cost F hc k hk hB
  refine ⟨beta, hbeta, ?_⟩
  rw [actualSignedPhaseDensity_integral F hc (by omega : 1 ≤ k) beta hbeta]
  have hA := actualOmittedMoment_nonneg F (2*k-2)
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end
end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_candidate_exists_signed_phase_integral
