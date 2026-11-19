import SpringerLean.Round747ActualAnnulusConvex
import SpringerLean.Round09OmittedLimit

open MeasureTheory Set Metric Filter
open scoped Topology

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- Removing the center point does not alter a planar area integral. -/
theorem greenPolarRegion_zero_ae_ball (b : ℝ) :
    greenPolarRegion 0 b =ᵐ[volume] ball (0 : ℂ) b := by
  filter_upwards [(countable_singleton (0 : ℂ)).ae_notMem volume] with z hz
  have hzne : z ≠ 0 := by simpa only [mem_singleton_iff] using hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  simp only [greenPolarRegion, mem_setOf_eq, mem_ball, dist_zero_right,
    hn, true_and]

theorem unitDisk_eq_iUnion_scaleSeq_balls :
    (⋃ j : ℕ, ball (0 : ℂ) (omittedScaleSeq j)) = ball (0 : ℂ) 1 := by
  ext z
  constructor
  · intro hz
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz
    have hn : ‖z‖ < omittedScaleSeq j := by simpa only [mem_ball, dist_zero_right] using hj
    simpa only [mem_ball, dist_zero_right] using hn.trans (omittedScaleSeq_lt_one j)
  · intro hz
    have hn : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
    obtain ⟨j,hj⟩ := (omittedScaleSeq_tendsto_one.eventually (eventually_gt_nhds hn)).exists
    exact mem_iUnion.mpr ⟨j, by simpa only [mem_ball, dist_zero_right] using hj⟩

/-- Genuine L1 integrability, with continuity required only INSIDE D. -/
theorem integrableOn_unitDisk_of_continuousOn_bound
    (f : ℂ → ℝ) (hf : ContinuousOn f (ball (0 : ℂ) 1))
    (M : ℝ) (hM : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ M) :
    IntegrableOn f (ball (0 : ℂ) 1) := by
  let D : Set ℂ := ball 0 1
  let μ : Measure ℂ := volume.restrict D
  have hD : MeasurableSet D := isOpen_ball.measurableSet
  have hb : Bornology.IsBounded D :=
    (isCompact_closedBall (0 : ℂ) 1).isBounded.subset ball_subset_closedBall
  haveI : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using hb.measure_lt_top⟩
  apply (integrable_const M : Integrable (fun _ : ℂ => M) μ).mono' (hf.aestronglyMeasurable hD)
  filter_upwards [ae_restrict_mem hD] with z hz
  exact hM z hz

/-- Passing actual smaller-disk comparisons to D uses true integrability
and an increasing exhaustion, without a unit-boundary extension. -/
theorem unitDisk_integral_le_of_innerBall_le
    (f g : ℂ → ℝ) (hf : IntegrableOn f (ball (0 : ℂ) 1))
    (hg : IntegrableOn g (ball (0 : ℂ) 1))
    (hsmall : ∀ b : ℝ, 0 < b → b < 1 →
      (∫ z in ball (0 : ℂ) b, f z) ≤ ∫ z in ball (0 : ℂ) b, g z) :
    (∫ z in ball (0 : ℂ) 1, f z) ≤ ∫ z in ball (0 : ℂ) 1, g z := by
  let S : ℕ → Set ℂ := fun j => ball 0 (omittedScaleSeq j)
  have hm : ∀ j, MeasurableSet (S j) := fun j => isOpen_ball.measurableSet
  have hmono : Monotone S := by
    intro i j hij
    exact ball_subset_ball (omittedScaleSeq_mono hij)
  have hfU : IntegrableOn f (⋃ j, S j) := by simpa only [S, unitDisk_eq_iUnion_scaleSeq_balls] using hf
  have hgU : IntegrableOn g (⋃ j, S j) := by simpa only [S, unitDisk_eq_iUnion_scaleSeq_balls] using hg
  have hfl := tendsto_setIntegral_of_monotone hm hmono hfU
  have hgl := tendsto_setIntegral_of_monotone hm hmono hgU
  simp only [S, unitDisk_eq_iUnion_scaleSeq_balls] at hfl hgl
  apply le_of_tendsto_of_tendsto hfl hgl
  filter_upwards [] with j
  exact hsmall (omittedScaleSeq j) (omittedScaleSeq_pos j) (omittedScaleSeq_lt_one j)

end SpringerLean

#print axioms SpringerLean.unitDisk_integral_le_of_innerBall_le
