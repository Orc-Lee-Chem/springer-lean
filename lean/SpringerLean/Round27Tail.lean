import SpringerLean.Round27ActualTruncation

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

/-- An integrable compensated whole-line kernel has a vanishing tail
outside expanding symmetric finite windows. This keeps the difference as
one integrable function throughout the limit. -/
theorem integrable_symmetric_complement_tail_tendsto_zero
    {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun n : ℕ =>
      ∫ t in (Icc (-(n : ℝ)) (n : ℝ))ᶜ, f t)
      atTop (𝓝 0) := by
  let S : ℕ → Set ℝ := fun n => (Icc (-(n : ℝ)) (n : ℝ))ᶜ
  have hanti : Antitone S := by
    intro i j hij t ht
    change t ∉ Icc (-(j : ℝ)) (j : ℝ) at ht
    change t ∉ Icc (-(i : ℝ)) (i : ℝ)
    intro hi
    apply ht
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact ⟨by linarith [hi.1], by linarith [hi.2]⟩
  have hinter : (⋂ n : ℕ, S n) = ∅ := by
    ext t
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro ht
    obtain ⟨n, hn⟩ := exists_nat_gt |t|
    have htn : t ∈ Icc (-(n : ℝ)) (n : ℝ) := by
      have habs := abs_lt.mp hn
      exact ⟨le_of_lt habs.1, le_of_lt habs.2⟩
    exact ht n htn
  have htend := tendsto_setIntegral_of_antitone
    (f := f) (s := S)
    (fun n => measurableSet_Icc.compl) hanti
    ⟨0, hf.integrableOn⟩
  simpa only [hinter, setIntegral_empty, S] using htend

/-- Actual compensated vertical differences have vanishing symmetric tails
at every fixed horizontal coordinate. Uniformity in an angularly varying
coordinate is a separate remaining obligation. -/
theorem regularExterior_vertical_difference_tail_tendsto_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (a : ℝ) :
    Tendsto (fun n : ℕ =>
      ∫ t in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
        regularExteriorVerticalPotentialDifference F s ξ a t)
      atTop (𝓝 0) :=
  integrable_symmetric_complement_tail_tendsto_zero
    (regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a)

end SpringerLean