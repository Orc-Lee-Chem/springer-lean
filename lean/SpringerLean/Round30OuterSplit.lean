import SpringerLean.Round30ShiftedTailUniform

open MeasureTheory Set

namespace SpringerLean

/-- Split a compensated integral outside a smaller window into the finite
annulus between two windows and the remaining outer tail. -/
theorem integral_compl_eq_sdiff_add_compl
    (f : ℝ → ℝ) (hf : Integrable f)
    (S M : Set ℝ) (hS : MeasurableSet S) (hM : MeasurableSet M)
    (hSM : S ⊆ M) :
    (∫ t in Sᶜ, f t) = (∫ t in M \ S, f t) + (∫ t in Mᶜ, f t) := by
  have hSsplit := integral_add_compl hS hf
  have hMsplit := integral_add_compl hM hf
  have hdiff := setIntegral_sdiff hS hf.integrableOn hSM
  linarith

end SpringerLean