import SpringerLean.Round1688ActualKnotLevelMeasurable
import Mathlib.Analysis.Calculus.FDeriv.Measurable

namespace SpringerLean

theorem actualHarmonicMultiplierTime_coordinateFderiv_measurable
    (F : ℂ → ℂ) (k : ℕ) (v : ℂ) :
    Measurable (fun z : ℂ =>
      (fderiv ℝ (actualHarmonicMultiplierTime F k) z) v) :=
  measurable_fderiv_apply_const ℝ (actualHarmonicMultiplierTime F k) v

/-- The exceptional points on a fixed physical-time level with a
nonzero chosen directional derivative form a measurable set inside
the actual regular source region. -/
theorem actualHarmonicMultiplierTime_badLevel_measurable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (c : ℝ) (v : ℂ) :
    MeasurableSet {z : ℂ | z ∈ actualMultiplierRegularSet F ∧
      actualHarmonicMultiplierTime F k z = c ∧
      (fderiv ℝ (actualHarmonicMultiplierTime F k) z) v ≠ 0} := by
  have hlevel := actualHarmonicMultiplierTime_level_measurable F hc k c
  have hderiv : MeasurableSet {z : ℂ |
      (fderiv ℝ (actualHarmonicMultiplierTime F k) z) v ≠ 0} :=
    (isClosed_singleton.isOpen_compl.measurableSet).preimage
      (actualHarmonicMultiplierTime_coordinateFderiv_measurable F k v)
  have hset :
      {z : ℂ | z ∈ actualMultiplierRegularSet F ∧
        actualHarmonicMultiplierTime F k z = c ∧
        (fderiv ℝ (actualHarmonicMultiplierTime F k) z) v ≠ 0} =
      {z : ℂ | z ∈ actualMultiplierRegularSet F ∧
        actualHarmonicMultiplierTime F k z = c} ∩
      {z : ℂ | (fderiv ℝ (actualHarmonicMultiplierTime F k) z) v ≠ 0} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  rw [hset]
  exact hlevel.inter hderiv

end SpringerLean

#print axioms SpringerLean.actualHarmonicMultiplierTime_badLevel_measurable
