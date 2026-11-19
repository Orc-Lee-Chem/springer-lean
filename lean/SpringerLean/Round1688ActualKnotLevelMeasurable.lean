import SpringerLean.Round1687ActualMultiplierRegularSet

namespace SpringerLean

/-- On an open set where a real function is continuous, each of its
restricted levels is measurable. -/
theorem measurableSet_level_of_continuousOn_open
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (S : Set α) (hS : IsOpen S) (f : α → ℝ)
    (hf : ContinuousOn f S) (c : ℝ) :
    MeasurableSet {x : α | x ∈ S ∧ f x = c} := by
  have hne : IsOpen (S ∩ f ⁻¹' ({c}ᶜ)) :=
    hf.isOpen_inter_preimage hS isClosed_singleton.isOpen_compl
  have hset : {x : α | x ∈ S ∧ f x = c} =
      S \ (S ∩ f ⁻¹' ({c}ᶜ)) := by
    ext x
    simp
  rw [hset]
  exact hS.measurableSet.diff hne.measurableSet

/-- The actual physical multiplier-time knot level is measurable on
the regular source region. -/
theorem actualHarmonicMultiplierTime_level_measurable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) :
    MeasurableSet {z : ℂ | z ∈ actualMultiplierRegularSet F ∧
      actualHarmonicMultiplierTime F k z = c} :=
  measurableSet_level_of_continuousOn_open
    (actualMultiplierRegularSet F)
    (actualMultiplierRegularSet_isOpen F hc)
    (actualHarmonicMultiplierTime F k)
    (actualHarmonicMultiplierTime_continuousOn_regularSet F hc k) c

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_level_measurable
