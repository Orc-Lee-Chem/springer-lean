import SpringerLean.Round1682LevelSetDerivative

open scoped Topology
open Filter MeasureTheory

namespace SpringerLean

/-- No global differentiability is needed: only the points of the fixed
level at which the derivative is nonzero enter the countable exceptional
set. This form is suited to multiplier times with singularities outside
the regular source domain. -/
theorem levelSet_nonzero_deriv_at_countable (f : ℝ → ℝ) (c : ℝ) :
    {x : ℝ | f x = c ∧ DifferentiableAt ℝ f x ∧ deriv f x ≠ 0}.Countable := by
  let s : Set ℝ := {x | f x = c}
  apply (countable_setOfPred_isolated_right_within (s := s)).mono
  intro x hx
  have hsx : x ∈ s := hx.1
  have hne : ∀ᶠ y in 𝓝[≠] x, f y ≠ c := by
    have h := hx.2.1.hasDerivAt.eventually_ne (c := c) hx.2.2
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

theorem ae_deriv_zero_on_level_of_differentiableAt
    (f : ℝ → ℝ) (c : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      DifferentiableAt ℝ f x → f x = c → deriv f x = 0 := by
  have hcount := levelSet_nonzero_deriv_at_countable f c
  have hnot : ∀ᵐ x ∂(volume : Measure ℝ),
      x ∉ {x : ℝ | f x = c ∧ DifferentiableAt ℝ f x ∧ deriv f x ≠ 0} := by
    rw [ae_iff]
    simpa only [not_not, Set.mem_ofPred_eq] using
      hcount.measure_zero (volume : Measure ℝ)
  filter_upwards [hnot] with x hx hd hlevel
  by_contra hderiv
  exact hx ⟨hlevel, hd, hderiv⟩

end SpringerLean

#print axioms SpringerLean.levelSet_nonzero_deriv_at_countable
#print axioms SpringerLean.ae_deriv_zero_on_level_of_differentiableAt
