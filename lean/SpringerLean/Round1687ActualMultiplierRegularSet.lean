import SpringerLean.Round1608ActualMultiplierTimeRegularity

open Metric

namespace SpringerLean

/-- The open source region where the physical multiplier time has its
ordinary real differential. -/
def actualMultiplierRegularSet (F : ℂ → ℂ) : Set ℂ :=
  (ball (0 : ℂ) 1 ∩ (actualHarmonic F) ⁻¹' ({0}ᶜ)) ∩ ({0}ᶜ)

theorem actualMultiplierRegularSet_isOpen
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    IsOpen (actualMultiplierRegularSet F) := by
  exact ((actualHarmonic_continuousOn_unitBall F hc).isOpen_inter_preimage
    isOpen_ball isClosed_singleton.isOpen_compl).inter
      isClosed_singleton.isOpen_compl

theorem actualMultiplierRegularSet_mem_iff (F : ℂ → ℂ) (z : ℂ) :
    z ∈ actualMultiplierRegularSet F ↔
      ‖z‖ < 1 ∧ actualHarmonic F z ≠ 0 ∧ z ≠ 0 := by
  simp [actualMultiplierRegularSet, and_assoc]

theorem actualHarmonicMultiplierTime_continuousOn_regularSet
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (k : ℕ) :
    ContinuousOn (actualHarmonicMultiplierTime F k)
      (actualMultiplierRegularSet F) := by
  intro z hz
  obtain ⟨hzball, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hz
  exact (actualHarmonicMultiplierTime_differentiableAt
    F hc k hzball hz0 hH).continuousAt.continuousWithinAt

end SpringerLean

#print axioms SpringerLean.actualMultiplierRegularSet_isOpen
#print axioms SpringerLean.actualHarmonicMultiplierTime_continuousOn_regularSet
