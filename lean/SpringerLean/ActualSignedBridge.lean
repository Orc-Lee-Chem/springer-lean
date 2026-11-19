import SpringerLean.Round11Energy

open MeasureTheory Metric

namespace SpringerLean.AnalyticRevision

/-- The normalized potential written directly with the actual phase field.
    This expression unfolds to actualHarmonicPhasePotential in Round1570. -/
noncomputable def diskPotential (F : ℂ → ℂ) (k : ℕ) (β : ℂ) : ℝ :=
  Real.pi⁻¹ * ∫ z in ball (0 : ℂ) 1,
    (actualHarmonicPhaseField F k β z)^2 / ‖actualHarmonic F z‖^2

/-- Conditional bridge. Its only analytic input beyond the original function
    class is the new global 7/3 energy estimate for this actual F and order k. -/
theorem signedCost_of_singleRampEnergy
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) (hk : 1 ≤ k)
    (henergy : ∀ β : ℂ, ‖β‖ = 1 →
      (k : ℝ)^2 * diskPotential F k β ≤ (7/3 : ℝ) * actualHarmonicPhaseEnergy F k β) :
    ∃ β : ℂ, ‖β‖ = 1 ∧
      ‖exteriorInverseCoeff F (2*k-1)‖ ≤
        actualHarmonicMoment F (2*k-2) - (3/14 : ℝ)*diskPotential F k β -
          actualOmittedMoment F (2*k-2)/2 := by
  obtain ⟨β, hβ, hidentity⟩ := exists_actualHarmonicPhaseEnergy_identity F hc hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hden : 0 < 2*(k : ℝ)^2 := by positivity
  have hfrac : (3/14 : ℝ)*diskPotential F k β ≤
      actualHarmonicPhaseEnergy F k β/(2*(k : ℝ)^2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [henergy β hβ]
  exact ⟨β, hβ, by linarith⟩

#print axioms signedCost_of_singleRampEnergy
end SpringerLean.AnalyticRevision
