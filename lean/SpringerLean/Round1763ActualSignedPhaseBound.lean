import SpringerLean.Round1762ActualGlobalPhaseEnergy

namespace SpringerLean

/-- The actual inverse coefficient selects a unit phase for which
the disk moment pays the signed phase potential with coefficient
8/25. The omitted-set moment is retained with its exact sign. -/
theorem exteriorInverseCoeff_exists_signed_phase_bound
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) :
    ∃ beta : ℂ, ‖beta‖ = 1 ∧
      ‖exteriorInverseCoeff F (2*k-1)‖ ≤
        actualHarmonicMoment F (2*k-2) -
          (8 / 25 : ℝ)*actualHarmonicPhasePotential F k beta -
          actualOmittedMoment F (2*k-2)/2 := by
  obtain ⟨beta, hbeta, hid⟩ := exists_actualHarmonicPhaseEnergy_identity
    F hc (k := k) (by omega)
  have hE := actualHarmonicPhase_energy_le_twentyfive_sixteenths
    F hc k hk beta hbeta
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hden : 0 < 2*(k : ℝ)^2 := by positivity
  have hfrac : (8 / 25 : ℝ)*actualHarmonicPhasePotential F k beta ≤
      actualHarmonicPhaseEnergy F k beta/(2*(k : ℝ)^2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [hE]
  exact ⟨beta, hbeta, by linarith [hid, hfrac]⟩

/-- A Catalan candidate, including equality, forces the signed
actual phase cost to reach the Catalan target. -/
theorem exteriorInverseCoeff_candidate_exists_signed_phase_cost
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖) :
    ∃ beta : ℂ, ‖beta‖ = 1 ∧
      (catalan (k-1) : ℝ) ≤ actualHarmonicMoment F (2*k-2) -
        (8 / 25 : ℝ)*actualHarmonicPhasePotential F k beta -
        actualOmittedMoment F (2*k-2)/2 := by
  obtain ⟨beta, hbeta, hcost⟩ :=
    exteriorInverseCoeff_exists_signed_phase_bound F hc k hk
  exact ⟨beta, hbeta, hB.trans hcost⟩

end SpringerLean

#print axioms SpringerLean.exteriorInverseCoeff_exists_signed_phase_bound
#print axioms SpringerLean.exteriorInverseCoeff_candidate_exists_signed_phase_cost
