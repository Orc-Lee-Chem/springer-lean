import SpringerLean.Round1379AngleSubstitution
import SpringerLean.Round30AnglePair
import Mathlib.Analysis.Convex.Continuous

open MeasureTheory

namespace SpringerLean

/-- A continuous even cosine test on the normalized circle is one
positive semicircle integral divided by `π`. -/
theorem evenCos_circleAverage_eq_integral (g : ℝ → ℝ)
    (hg : Continuous g) :
    Real.circleAverage (fun ζ : ℂ => g (2*ζ.re)) 0 1 =
      (1/Real.pi) * (∫ θ in (0:ℝ)..Real.pi, g (2*Real.cos θ)) := by
  let f : ℝ → ℝ := fun θ => g (2*Real.cos θ)
  have hfcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hper : Function.Periodic f (2*Real.pi) := by
    intro θ
    simp [f, Real.cos_add_two_pi]
  have hint : IntervalIntegrable f volume (-Real.pi) Real.pi :=
    hfcont.intervalIntegrable _ _
  have hpair := periodic_angle_integral_pair f hper hint
  have heven (θ : ℝ) : f (-θ) = f θ := by simp [f, Real.cos_neg]
  simp_rw [heven] at hpair
  rw [Real.circleAverage_eq_integral_add 0]
  simp_rw [circleMap_zero_re]
  simp only [one_mul, add_zero]
  change (2*Real.pi)⁻¹ * (∫ θ in (0:ℝ)..2*Real.pi, f θ) = _
  rw [hpair]
  simp_rw [← two_mul]
  rw [intervalIntegral.integral_const_mul]
  dsimp [f]
  ring

theorem coarseInverseRadius_continuous : Continuous coarseInverseRadius := by
  have hc := coarseInverseRadius_convexOn.continuousOn isOpen_univ
  simpa using hc

end SpringerLean

#print axioms SpringerLean.evenCos_circleAverage_eq_integral
#print axioms SpringerLean.coarseInverseRadius_continuous
