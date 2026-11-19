import SpringerLean.Round2130ReciprocalExteriorDomain
import SpringerLean.Round2029ExteriorMapUniqueness
import Mathlib.Analysis.Complex.Schwarz

open Set Metric Filter Function
open scoped Topology

namespace SpringerLean

/-- Actual disk uniformization data, with infinity represented by the
origin of the reciprocal domain. Existence is a separate theorem. -/
structure ReciprocalDiskUniformization (K : Set ℂ) (a : ℂ) where
  toFun : ℂ → ℂ
  differentiable : DifferentiableOn ℂ toFun (ball 0 1)
  bijective : BijOn toFun (ball 0 1) (reciprocalExteriorDomain K a)
  map_zero : toFun 0 = 0

theorem analyticAt_invFunOn_of_open_injOn
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) (z : ℂ) (hz : z ∈ U) :
    AnalyticAt ℂ (invFunOn f U) (f z) := by
  have ha : AnalyticAt ℂ f z := hf.analyticAt (hU.mem_nhds hz)
  have hd := deriv_ne_zero_of_differentiableOn_injOn hU hf hi hz
  let R := ha.hasStrictDerivAt.localInverse f (deriv f z) z hd
  have hR0 : R (f z) = z :=
    HasStrictFDerivAt.localInverse_apply_image (ha.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  have hR : AnalyticAt ℂ R (f z) := ha.analyticAt_localInverse hd
  have hmem : ∀ᶠ w in 𝓝 (f z), R w ∈ U := hR.continuousAt.eventually (hR0.symm ▸ hU.mem_nhds hz)
  have he : ∀ᶠ w in 𝓝 (f z), f (R w) = w := ha.hasStrictDerivAt.eventually_right_inverse hd
  apply hR.congr
  filter_upwards [hmem,he] with w hw hfw
  have hwg : w ∈ f '' U := ⟨R w,hw,hfw⟩
  exact hi hw (invFunOn_mem hwg) (hfw.trans (invFunOn_eq hwg).symm)

theorem reciprocalDiskUniformization_inverse_analyticAt
    {K : Set ℂ} {a : ℂ} (f : ReciprocalDiskUniformization K a)
    (z : ℂ) (hz : z ∈ reciprocalExteriorDomain K a) :
    AnalyticAt ℂ (invFunOn f.toFun (ball 0 1)) z := by
  obtain ⟨w,hw,rfl⟩ := f.bijective.2.2 hz
  exact analyticAt_invFunOn_of_open_injOn _ _ isOpen_ball f.differentiable f.bijective.2.1 _ hw

theorem holomorphic_disk_selfMap_eq_id_of_nonzero_fixed_point
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1)) (hm : MapsTo f (ball 0 1) (ball 0 1))
    (h0 : f 0 = 0) (z : ℂ) (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) (hfix : f z = z) :
    EqOn f id (ball 0 1) := by
  have hMaps : MapsTo f (ball (0:ℂ) 1) (closedBall (f 0) 1) := by
    rw [h0]
    exact fun x hx => ball_subset_closedBall (hm hx)
  have hds : dslope f 0 z = (1:ℂ) := by
    rw [dslope_of_ne f hz0,slope_def_field,sub_zero,hfix,h0,sub_zero,div_self hz0]
  have h := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hf hMaps hz
    (by rw [hds,norm_one,div_one])
  intro w hw
  simpa only [h0,hds,sub_zero,smul_eq_mul,mul_one,zero_add,id_eq] using h hw

end SpringerLean
