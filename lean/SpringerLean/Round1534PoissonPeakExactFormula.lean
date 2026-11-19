import SpringerLean.Round1533PoissonPeakArcIdentity

open MeasureTheory Set

namespace SpringerLean
set_option maxHeartbeats 320000

/-- The cap's Poisson mass in the one-turn probability normalization. -/
noncomputable def flattenedCapPoissonMass (h r : ℝ) : ℝ :=
  Real.pi⁻¹ *
    (∫ θ in Ioc (0:ℝ) h,
      poissonKernel 0 (r:ℂ) (circleMap 0 1 θ))

/-- Exact peak-deficit identity, before bounding the complementary arc. -/
theorem flattenedCosinePoisson_peak_defect_exact
    {h r : ℝ} (hh0 : 0 < h) (hhpi : h < Real.pi)
    (hr0 : 0 < r) (hr1 : r < 1) :
    let d := 2-2*Real.sin h/h
    2*r-flattenedCosinePoissonAtReal h r =
      (d+(1-r)^2/r)*flattenedCapPoissonMass h r -
        (1-r^2)*h/(Real.pi*r) := by
  dsimp only
  have hhalf := flattenedCosinePoisson_peak_defect_half_arc
    hh0 hhpi hr0 hr1
  have hlocal := centeredPoisson_arc_defect_integral hr0 hr1 hh0.le
    (d:=2-2*Real.sin h/h)
  rw [hlocal] at hhalf
  dsimp [flattenedCapPoissonMass]
  rw [hhalf]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  ring

end SpringerLean

#print axioms SpringerLean.flattenedCosinePoisson_peak_defect_exact
