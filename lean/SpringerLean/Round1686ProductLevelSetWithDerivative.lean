import SpringerLean.Round1684LocalLevelSetDerivative
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace SpringerLean

/-- A product-space level-set rule with an explicitly supplied partial
derivative on a measurable regular set. This formulation lets the
actual multiplier time use its already proved directional fderiv,
without requiring its singular extension to be differentiable. -/
theorem ae_second_derivative_value_zero_on_level
    (f g : ℝ × ℝ → ℝ) (c : ℝ) (S : Set (ℝ × ℝ))
    (hderiv : ∀ p ∈ S,
      DifferentiableAt ℝ (fun v => f (p.1, v)) p.2 ∧
      deriv (fun v => f (p.1, v)) p.2 = g p)
    (hMeas : MeasurableSet {p : ℝ × ℝ | p ∈ S ∧ f p = c ∧ g p ≠ 0}) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      p ∈ S → f p = c → g p = 0 := by
  let bad : Set (ℝ × ℝ) := {p | p ∈ S ∧ f p = c ∧ g p ≠ 0}
  have hsection (x : ℝ) :
      (volume : Measure ℝ) (Prod.mk x ⁻¹' bad) = 0 := by
    have hsub : Prod.mk x ⁻¹' bad ⊆
        {v : ℝ | f (x, v) = c ∧
          DifferentiableAt ℝ (fun w => f (x, w)) v ∧
          deriv (fun w => f (x, w)) v ≠ 0} := by
      intro v hv
      have hpoint : (x, v) ∈ S ∧ f (x, v) = c ∧ g (x, v) ≠ 0 := hv
      obtain ⟨hdiff, heq⟩ := hderiv (x, v) hpoint.1
      exact ⟨hpoint.2.1, hdiff, heq.symm ▸ hpoint.2.2⟩
    exact ((levelSet_nonzero_deriv_at_countable
      (fun v => f (x, v)) c).mono hsub).measure_zero (volume : Measure ℝ)
  have hsections :
      (fun x : ℝ => (volume : Measure ℝ) (Prod.mk x ⁻¹' bad))
        =ᵐ[(volume : Measure ℝ)] (fun _ => 0) :=
    Filter.Eventually.of_forall hsection
  have hbad : ((volume : Measure ℝ).prod (volume : Measure ℝ)) bad = 0 :=
    Measure.measure_prod_null_of_ae_null hMeas hsections
  have hnot : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), p ∉ bad := by
    rw [ae_iff]
    simpa only [not_not, bad, Set.mem_ofPred_eq] using hbad
  filter_upwards [hnot] with p hp hS hc
  by_contra hg
  exact hp ⟨hS, hc, hg⟩

end SpringerLean

#print axioms SpringerLean.ae_second_derivative_value_zero_on_level
