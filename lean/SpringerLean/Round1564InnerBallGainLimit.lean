import SpringerLean.Round1563ActualAnyAnnulusGainNonneg
import SpringerLean.Round748UnitDiskLimit

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean
set_option maxHeartbeats 640000

/-- A strict gain obtained on one compact interior ball survives the
unit-disk exhaustion if all outer radial increments are nonnegative. -/
theorem unitDisk_integral_ge_of_innerBall_mono
    (f : ℂ → ℝ) (hf : IntegrableOn f (ball (0:ℂ) 1))
    {b₀ : ℝ} (hb₀ : b₀ < 1)
    (hmono : ∀ b : ℝ, b₀ ≤ b → b < 1 →
      (∫ z in ball (0:ℂ) b₀, f z) ≤ ∫ z in ball (0:ℂ) b, f z) :
    (∫ z in ball (0:ℂ) b₀, f z) ≤
      ∫ z in ball (0:ℂ) 1, f z := by
  let S : ℕ → Set ℂ := fun j => ball 0 (omittedScaleSeq j)
  have hm : ∀ j, MeasurableSet (S j) := fun _ => isOpen_ball.measurableSet
  have hSmono : Monotone S := by
    intro i j hij
    exact ball_subset_ball (omittedScaleSeq_mono hij)
  have hfU : IntegrableOn f (⋃ j, S j) := by
    simpa only [S, unitDisk_eq_iUnion_scaleSeq_balls] using hf
  have hlim := tendsto_setIntegral_of_monotone hm hSmono hfU
  simp only [S, unitDisk_eq_iUnion_scaleSeq_balls] at hlim
  have hnear : ∀ᶠ j : ℕ in atTop, b₀ ≤ omittedScaleSeq j := by
    have h := omittedScaleSeq_tendsto_one.eventually (eventually_gt_nhds hb₀)
    filter_upwards [h] with j hj
    exact hj.le
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [hnear] with j hj
  exact hmono (omittedScaleSeq j) hj (omittedScaleSeq_lt_one j)

end SpringerLean

#print axioms SpringerLean.unitDisk_integral_ge_of_innerBall_mono
