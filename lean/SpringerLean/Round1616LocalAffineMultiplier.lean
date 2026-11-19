import SpringerLean.Round1615ActualRadialMultiplierComposition

open Filter
open scoped Topology

namespace SpringerLean

/-- A locally affine multiplier has precisely its printed slope. -/
theorem deriv_of_eventually_affine
    (f : ℝ → ℝ) (t0 v slope : ℝ)
    (hloc : f =ᶠ[𝓝 t0] fun s => v+slope*(s-t0)) :
    DifferentiableAt ℝ f t0 ∧ deriv f t0 = slope := by
  have ha : HasDerivAt (fun s : ℝ => v+slope*(s-t0)) slope t0 := by
    convert (hasDerivAt_const t0 v).add
      (((hasDerivAt_id t0).sub_const t0).const_mul slope) using 1
    · funext s
      simp only [Pi.add_apply, id_eq]
    · ring
  have hf : HasDerivAt f slope t0 :=
    ha.congr_of_eventuallyEq hloc
  exact ⟨hf.differentiableAt, hf.deriv⟩

end SpringerLean

#print axioms SpringerLean.deriv_of_eventually_affine
