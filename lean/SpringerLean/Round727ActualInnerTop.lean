import SpringerLean.Round725RegularInnerTop
import SpringerLean.Round726ActualTopRegularization

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Sharp raw top-mass integral for EVERY actual map in the paper's
original class.  There is no remaining s, boundary regularity, optimizer
or circle-rearrangement hypothesis. -/
theorem actualAngularTopValue_le_sine
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r h : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hh0 : 0 < h) (hhpi : h < Real.pi) :
    actualAngularTopValue F c r h ≤ 4*r*Real.sin h := by
  obtain ⟨M, hM0, hM⟩ := actualAngularTopValue_exists_regularization_error F hc hr0 hr1
  have hlim : Tendsto (fun s : ℝ => 4*r*Real.sin h+4*h*M*r*(1-s))
      (𝓝[<] (1 : ℝ)) (𝓝 (4*r*Real.sin h)) := by
    have hcont : ContinuousAt (fun s : ℝ => 4*r*Real.sin h+4*h*M*r*(1-s)) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  have hs1 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), s < 1 := self_mem_nhdsWithin
  have hs0 : Ioi (0 : ℝ) ∈ 𝓝[<] (1 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hs1, hs0] with s hs1 hs0
  have he := hM s hs0 hs1 c h hh0 hhpi
  rw [hcn, mul_one] at he
  have hl := (abs_le.mp he).1
  have hv := regularExterior_actualAngularTopValue_le_sine F hc hs0 hs1 c hcn hr0 hr1 hh0 hhpi
  linarith

/-- Arbitrary measurable angular candidates, on the SAME actual inner
circle, are controlled by the equal-mass centered slit arc.  Both the
integral and the mass use RAW angle, not probability normalization. -/
theorem actualHarmonic_projected_set_le_sine_of_raw_mass
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (c : ℂ) (hcn : ‖c‖ = 1)
    {r h : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hh0 : 0 < h) (hhpi : h < Real.pi)
    (A : Set ℝ) (hAm : MeasurableSet A) (hAs : A ⊆ Ioc 0 (2*Real.pi))
    (hmass : volume A = ENNReal.ofReal (2*h)) :
    (∫ θ in A, (c*actualHarmonic F (circleMap 0 r θ)).re) ≤ 4*r*Real.sin h := by
  exact (actualAngularTopValue_candidate_le F hc c hr0 hr1 hh0 hhpi A
    ⟨hAm, hAs, hmass⟩).trans (actualAngularTopValue_le_sine F hc c hcn hr0 hr1 hh0 hhpi)

end SpringerLean

#print axioms SpringerLean.actualAngularTopValue_le_sine
#print axioms SpringerLean.actualHarmonic_projected_set_le_sine_of_raw_mass
