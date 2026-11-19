import SpringerLean.Round26ShiftDirection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

open MeasureTheory Set Filter
open scoped Topology
open scoped ENNReal


namespace SpringerLean

/-- The actual indicator of a bounded measurable real set has an
everywhere-defined interval primitive differentiable almost everywhere,
with the indicator as its derivative at those points. -/
theorem bounded_indicator_ae_hasDerivAt_primitive
    (E : Set ℝ) (hE : MeasurableSet E) (hEb : Bornology.IsBounded E) :
    ∀ᵐ x : ℝ, HasDerivAt
      (fun y : ℝ => ∫ t in (0 : ℝ)..y,
        E.indicator (fun _ => (1 : ℝ)) t)
      (E.indicator (fun _ => (1 : ℝ)) x) x := by
  have hfinite : volume E ≠ ∞ := hEb.measure_lt_top.ne
  have hint : Integrable (E.indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const hfinite).integrable_indicator hE
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    hint.locallyIntegrable] with x hx
  exact hx 0

/-- A classical derivative gives the precise left difference quotient
needed for two separated density transitions. -/
theorem HasDerivAt.tendsto_left_difference_quotient
    {P : ℝ → ℝ} {x c : ℝ} (hP : HasDerivAt P c x) :
    Tendsto (fun d : ℝ => (P x - P (x - d)) / d)
      (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have hneg : Tendsto (fun d : ℝ => -d)
      (𝓝[>] (0 : ℝ)) (𝓝[<] (0 : ℝ)) := by
    simpa using (tendsto_neg_nhdsGT_neg (a := (0 : ℝ)))
  have h := hP.tendsto_slope_zero_left.comp hneg
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  dsimp
  have hd0 : d ≠ 0 := ne_of_gt hd
  field_simp
  ring

end SpringerLean
