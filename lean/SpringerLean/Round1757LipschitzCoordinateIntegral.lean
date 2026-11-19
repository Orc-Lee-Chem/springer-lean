import SpringerLean.Round1739LipschitzSliceFTC
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Set intervalIntegral
open scoped Topology

namespace SpringerLean

theorem deriv_zero_outside_unit_support
    (f : ℝ → ℝ) (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0)
    {x : ℝ} (hx : 1 < |x|) : deriv f x = 0 := by
  have heq : f =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [continuous_abs.continuousAt.eventually (lt_mem_nhds hx)]
      with y hy
    exact hzero y hy.le
  simpa using heq.deriv_eq

/-- A compactly supported Lipschitz real function has integrable
ordinary derivative with zero integral, even at nonsmooth points. -/
theorem integral_deriv_zero_of_lipschitz_unit_support
    (f : ℝ → ℝ) (K : NNReal) (hf : LipschitzWith K f)
    (hzero : ∀ x : ℝ, 1 ≤ |x| → f x = 0) :
    Integrable (deriv f) ∧ (∫ x : ℝ, deriv f x) = 0 := by
  have hbound (x : ℝ) : ‖deriv f x‖ ≤ (K : ℝ) :=
    norm_deriv_le_of_lipschitz hf
  have hInt : IntegrableOn (deriv f) (Ioc (-2 : ℝ) 2) :=
    Measure.integrableOn_of_bounded (by simp)
      (measurable_deriv f).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hout (x : ℝ) (hx : x ∉ Ioc (-2 : ℝ) 2) : deriv f x = 0 := by
    apply deriv_zero_outside_unit_support f hzero
    by_contra h
    have hb := abs_le.mp (le_of_not_gt h)
    exact hx ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hFTC : (∫ x in (-2 : ℝ)..2, deriv f x) = 0 :=
    integral_deriv_zero_of_lipschitz_slice f (-2) 2 K hf.lipschitzOnWith
      (hzero (-2) (by norm_num)) (hzero 2 (by norm_num))
  refine ⟨hInt.integrable_of_forall_notMem_eq_zero hout, ?_⟩
  calc
    _ = ∫ x in Ioc (-2 : ℝ) 2, deriv f x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hout).symm
    _ = ∫ x in (-2 : ℝ)..2, deriv f x :=
      (intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)).symm
    _ = 0 := hFTC

end SpringerLean

#print axioms SpringerLean.integral_deriv_zero_of_lipschitz_unit_support
