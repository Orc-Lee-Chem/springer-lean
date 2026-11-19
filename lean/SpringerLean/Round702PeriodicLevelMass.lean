import SpringerLean.Round689PeriodicThreshold

open MeasureTheory Set
open scoped ENNReal

namespace SpringerLean
set_option Elab.async false

/-- A measurable periodic level set has the same raw mass in every turn.
This permits putting the cut in an excluded gap, without modulo folding. -/
theorem periodic_superlevel_turn_volume
    (f : ℝ → ℝ) (hf : Continuous f) {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (ell q : ℝ) :
    volume ({t | ell ≤ f t} ∩ Ioc q (q+T)) =
      volume ({t | ell ≤ f t} ∩ Ioc 0 T) := by
  classical
  let C : Set ℝ := {t | ell ≤ f t}
  let p : ℝ → ℝ := C.indicator (fun _ => 1)
  have hCm : MeasurableSet C := measurableSet_le measurable_const hf.measurable
  have hper : Function.Periodic p T := by
    intro t
    simp only [p, C, indicator_apply, mem_setOf_eq, hp t]
  have hreal (a : ℝ) :
      (∫ t in Ioc a (a+T), p t) = volume.real (C ∩ Ioc a (a+T)) := by
    change (∫ t in Ioc a (a+T), C.indicator (fun _ => (1 : ℝ)) t) = _
    rw [integral_indicator hCm, setIntegral_const]
    simp only [smul_eq_mul, mul_one, Measure.real_def, Measure.restrict_apply hCm]
  have heq : volume.real (C ∩ Ioc q (q+T)) =
      volume.real (C ∩ Ioc 0 T) := by
    rw [← hreal q, show Ioc 0 T = Ioc 0 (0+T) by rw [zero_add], ← hreal 0]
    simp only [zero_add]
    rw [← intervalIntegral.integral_of_le (by linarith : q ≤ q+T),
      ← intervalIntegral.integral_of_le hT.le]
    simpa only [zero_add] using hper.intervalIntegral_add_eq q 0
  have hfin (a : ℝ) : volume (C ∩ Ioc a (a+T)) ≠ ∞ :=
    ne_of_lt ((measure_mono inter_subset_right).trans_lt (by
      rw [Real.volume_Ioc]
      finiteness))
  exact (ENNReal.toReal_eq_toReal_iff' (hfin q) (by simpa only [zero_add] using hfin 0)).mp heq

/-- A nontrivial finite turn-mass leaves a point strictly below the
threshold. No conclusion about interiors is inferred from positive mass. -/
theorem periodic_superlevel_exists_lt
    (f : ℝ → ℝ) (ell : ℝ) {T m : ℝ} (hT : 0 < T) (hm0 : 0 ≤ m)
    (hmT : m < T)
    (hmass : volume ({t | ell ≤ f t} ∩ Ioc 0 T) = ENNReal.ofReal m) :
    ∃ q : ℝ, f q < ell := by
  by_contra hn
  have hall : ∀ t : ℝ, ell ≤ f t := by
    intro t
    exact le_of_not_gt (fun ht => hn ⟨t, ht⟩)
  have heq : {t | ell ≤ f t} ∩ Ioc 0 T = Ioc 0 T := by
    ext t
    simp only [mem_inter_iff, mem_setOf_eq, and_iff_right_iff_imp]
    exact fun _ => hall t
  rw [heq, Real.volume_Ioc, sub_zero] at hmass
  have hle : T ≤ m := by
    have h := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal m ≠ ∞) hmass.le
    rw [ENNReal.toReal_ofReal hT.le, ENNReal.toReal_ofReal hm0] at h
    exact h
  linarith

end SpringerLean

#print axioms SpringerLean.periodic_superlevel_turn_volume
#print axioms SpringerLean.periodic_superlevel_exists_lt
