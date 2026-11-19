import SpringerLean.Round16Univalent
import SpringerLean.Round15Derivative

namespace SpringerLean

/-- The actual rescaled exterior map has no critical point in the original
open exterior disk. This follows from the general holomorphic-univalent
noncriticality theorem, with no new hypothesis on the paper's function class. -/
theorem rescaleExterior_deriv_ne_zero
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk) :
    deriv (rescaleExterior s F) v ≠ 0 := by
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z :=
    fun z hz => hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  have hG : DifferentiableOn ℂ (rescaleExterior s F) exteriorDisk := by
    intro z hz
    have hzabove : z ∈ exteriorAbove s := lt_trans hs1 hz
    exact (rescaleExterior_analyticAt hs0 hF hzabove).differentiableAt.differentiableWithinAt
  have hinj : Set.InjOn (rescaleExterior s F) exteriorDisk := by
    intro x hx y hy hxy
    exact rescaleExterior_injOn hs0 hc.2.1 (lt_trans hs1 hx)
      (lt_trans hs1 hy) hxy
  exact deriv_ne_zero_of_differentiableOn_injOn exteriorDisk_isOpen hG hinj hv

/-- The boundary logarithmic potential of every actual image value of the
regularized paper map, with only the original function-class assumptions. -/
theorem regularExterior_image_boundary_log_potential
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {v : ℂ} (hv : v ∈ exteriorDisk) :
    Real.circleAverage
      (fun ζ : ℂ => Real.log ‖rescaleExterior s F ζ - rescaleExterior s F v‖)
      0 1 = Real.log ‖v‖ := by
  exact regularExterior_image_boundary_log_potential_of_rescale_deriv_ne_zero
    F hc hs0 hs1 hv (rescaleExterior_deriv_ne_zero F hc hs0 hs1 hv)

end SpringerLean
