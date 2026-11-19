import SpringerLean.Round26Differentiation

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean

noncomputable def realSetIndicator (E : Set ℝ) : ℝ → ℝ :=
  E.indicator (fun _ => (1 : ℝ))

noncomputable def realSetPrimitive (E : Set ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, realSetIndicator E t

theorem realSetIndicator_integrable
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    Integrable (realSetIndicator E) := by
  exact (integrableOn_const hEb.measure_lt_top.ne).integrable_indicator hE

theorem realSetPrimitive_ae_hasDerivAt
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    ∀ᵐ x : ℝ, HasDerivAt (realSetPrimitive E) (realSetIndicator E x) x := by
  exact bounded_indicator_ae_hasDerivAt_primitive E hE hEb

/-- A difference of the indicator primitive is the oriented interval
integral. -/
theorem realSetPrimitive_sub_eq_interval
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a b : ℝ) :
    realSetPrimitive E b - realSetPrimitive E a =
      ∫ t in a..b, realSetIndicator E t := by
  have hp := realSetIndicator_integrable E hE hEb
  unfold realSetPrimitive
  exact intervalIntegral.integral_interval_sub_left
    hp.intervalIntegrable hp.intervalIntegrable

/-- The interval integral of an indicator is the real measure of the
intersection with that interval. -/
theorem realSetIndicator_interval_integral_eq_measureReal
    (E : Set ℝ) (hE : MeasurableSet E)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b, realSetIndicator E t) =
      volume.real (Ioc a b ∩ E) := by
  rw [intervalIntegral.integral_of_le hab]
  unfold realSetIndicator
  rw [setIntegral_indicator hE, setIntegral_const]
  simp

/-- Exact interval identity for one translated indicator. No limit is used
here. -/
theorem realSet_interval_shift_integral_eq
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E)
    (a b d : ℝ) :
    (∫ t in a..b, realSetIndicator E t - realSetIndicator E (t - d)) =
      (realSetPrimitive E b - realSetPrimitive E (b - d)) -
        (realSetPrimitive E a - realSetPrimitive E (a - d)) := by
  have hp : Integrable (realSetIndicator E) :=
    realSetIndicator_integrable E hE hEb
  have hps : IntervalIntegrable
      (fun t : ℝ => realSetIndicator E (t - d)) volume a b := by
    rw [intervalIntegrable_iff]
    have hcomp : Integrable (fun t : ℝ => realSetIndicator E (t - d)) := by
      exact hp.comp_sub_right d
    exact hcomp.integrableOn
  rw [intervalIntegral.integral_sub hp.intervalIntegrable hps,
    intervalIntegral.integral_comp_sub_right]
  have hbase (u v : ℝ) :
      (∫ t in u..v, realSetIndicator E t) =
        realSetPrimitive E v - realSetPrimitive E u := by
    unfold realSetPrimitive
    exact (intervalIntegral.integral_interval_sub_left
      hp.intervalIntegrable hp.intervalIntegrable).symm
  rw [hbase a b, hbase (a - d) (b - d)]
  ring

end SpringerLean
