import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open scoped Topology
open Filter MeasureTheory

namespace SpringerLean

/-- At a fixed level, points with a nonzero real derivative are isolated
on the right, hence form a countable set. -/
theorem levelSet_nonzero_deriv_countable (f : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, DifferentiableAt ℝ f x) :
    {x : ℝ | f x = c ∧ deriv f x ≠ 0}.Countable := by
  let s : Set ℝ := {x | f x = c}
  apply (countable_setOfPred_isolated_right_within (s := s)).mono
  intro x hx
  have hsx : x ∈ s := hx.1
  have hne : ∀ᶠ y in 𝓝[≠] x, f y ≠ c := by
    have h := (hf x).hasDerivAt.eventually_ne (c := c) hx.2
    simpa [hx.1] using h
  have hsub : s ∩ Set.Ioi x ⊆ {x}ᶜ := by
    intro y hy
    exact ne_of_gt hy.2
  have hne' : ∀ᶠ y in 𝓝[s ∩ Set.Ioi x] x, f y ≠ c :=
    hne.filter_mono (nhdsWithin_mono x hsub)
  have hmem : ∀ᶠ y in 𝓝[s ∩ Set.Ioi x] x, y ∈ s ∩ Set.Ioi x :=
    self_mem_nhdsWithin
  have heq : ∀ᶠ y in 𝓝[s ∩ Set.Ioi x] x, f y = c :=
    hmem.mono (fun y hy => hy.1)
  refine ⟨hsx, Filter.eventually_false_iff_eq_bot.mp ?_⟩
  exact (hne'.and heq).mono (fun _ hy => hy.1 hy.2)

/-- A fixed level has zero derivative almost everywhere with respect to
one-dimensional Lebesgue measure. -/
theorem ae_deriv_zero_on_level (f : ℝ → ℝ) (c : ℝ)
    (hf : ∀ x, DifferentiableAt ℝ f x) :
    ∀ᵐ x ∂(volume : Measure ℝ), f x = c → deriv f x = 0 := by
  have hcount := levelSet_nonzero_deriv_countable f c hf
  rw [ae_iff]
  simpa only [not_imp, not_not] using hcount.measure_zero (volume : Measure ℝ)

end SpringerLean

#print axioms SpringerLean.levelSet_nonzero_deriv_countable
#print axioms SpringerLean.ae_deriv_zero_on_level
