import SpringerLean.Round2109AngularLevelSlice
import SpringerLean.Round682FiniteQuantile

open MeasureTheory Set Real Bornology
open scoped ENNReal

namespace SpringerLean

theorem periodic_level_measure_turn
    (A : Set ℝ) (hA : MeasurableSet A) (T : ℝ) (hT : 0 < T)
    (hp : ∀ t : ℝ, t+T ∈ A ↔ t ∈ A) (q : ℝ) :
    volume.real (A ∩ Ioc q (q+T)) = volume.real (A ∩ Ioc 0 T) := by
  classical
  let f : ℝ → ℝ := A.indicator (fun _ => 1)
  have hf : Function.Periodic f T := by
    intro t
    by_cases ht : t ∈ A
    · simp [f,Set.indicator_of_mem ht,Set.indicator_of_mem ((hp t).2 ht)]
    · simp [f,Set.indicator_of_notMem ht,Set.indicator_of_notMem (fun h => ht ((hp t).1 h))]
  have h (a b : ℝ) (hab : a ≤ b) : (∫ t in a..b, f t) = volume.real (A ∩ Ioc a b) := by
    unfold f
    rw [intervalIntegral.integral_of_le hab,integral_indicator hA,Measure.restrict_restrict hA,
      integral_const,smul_eq_mul,measureReal_restrict_apply_univ,mul_one]
  rw [← h q (q+T) (by linarith : q ≤ q+T), ← h 0 T hT.le]
  simpa only [zero_add] using hf.intervalIntegral_add_eq q 0

/-- The same threshold controls strict and weak level masses after
every angular cut. The level set at the threshold may have positive mass. -/
theorem periodic_exists_threshold_mass
    (f : ℝ → ℝ) (hf : Continuous f) (T m : ℝ) (hT : 0 < T)
    (hp : Function.Periodic f T) (hm : 0 < m) (hmt : m < T) :
    ∃ a : ℝ, ∀ q : ℝ,
      volume.real ({t | a < f t} ∩ Ioc q (q+T)) ≤ m ∧
      m ≤ volume.real ({t | a ≤ f t} ∩ Ioc q (q+T)) := by
  let I := Ioc (0:ℝ) T
  let μ := volume.restrict I
  have hμ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (Metric.isBounded_Ioc _ _).measure_lt_top.ne
  obtain ⟨B,hB⟩ := (hp.isBounded_of_continuous hT.ne' hf).exists_norm_le
  have hbd (x : ℝ) : |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hB (f x) (mem_range_self x)
  have hbelow (x : ℝ) : -B ≤ -f x := by linarith [(abs_le.mp (hbd x)).2]
  have hfull : ∃ R : ℝ, ENNReal.ofReal m ≤ μ {x | -f x ≤ R} := by
    refine ⟨B,?_⟩
    have he : {x : ℝ | -f x ≤ B} = univ := by
      ext t
      simp only [mem_setOf_eq,mem_univ,iff_true]
      linarith [(abs_le.mp (hbd t)).1]
    rw [he,show μ univ = ENNReal.ofReal T by simp [μ,I,Real.volume_Ioc]]
    exact ENNReal.ofReal_le_ofReal hmt.le
  obtain ⟨ell,hl,hu⟩ := finiteMeasure_sublevel_threshold μ (fun t => -f t)
    hf.measurable.neg (-B) hbelow (ENNReal.ofReal m) (ENNReal.ofReal_pos.mpr hm) hfull
  let a := -ell
  have hs : {t : ℝ | -f t < ell} = {t | a < f t} := by ext; simp [a,neg_lt]
  have hw : {t : ℝ | -f t ≤ ell} = {t | a ≤ f t} := by ext; simp [a,neg_le]
  have hS : MeasurableSet {t : ℝ | a < f t} := measurableSet_lt measurable_const hf.measurable
  have hW : MeasurableSet {t : ℝ | a ≤ f t} := measurableSet_le measurable_const hf.measurable
  rw [hs,Measure.restrict_apply hS] at hl
  rw [hw,Measure.restrict_apply hW] at hu
  refine ⟨a,fun q => ⟨?_,?_⟩⟩
  · rw [periodic_level_measure_turn _ hS T hT (fun t => by simp [hp t]) q]
    exact (ENNReal.toReal_mono (by finiteness) hl).trans_eq (ENNReal.toReal_ofReal hm.le)
  · rw [periodic_level_measure_turn _ hW T hT (fun t => by simp [hp t]) q]
    have hfin : volume ({t : ℝ | a ≤ f t} ∩ I) ≠ ∞ :=
      ((Metric.isBounded_Ioc _ _).subset inter_subset_right).measure_lt_top.ne
    exact (ENNReal.toReal_ofReal hm.le).symm.trans_le (ENNReal.toReal_mono hfin hu)

end SpringerLean
