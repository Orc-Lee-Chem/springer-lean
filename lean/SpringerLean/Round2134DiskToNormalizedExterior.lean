import SpringerLean.Round2133ReciprocalDiskOddness
import SpringerLean.Round1953FactorScaling
import Mathlib.Analysis.Calculus.DSlope

open Set Metric Filter Function
open scoped Topology

namespace SpringerLean

private theorem inv_mem_disk_of_exterior (w : ℂ) (hw : w ∈ exteriorDisk) :
    w⁻¹ ∈ ball (0:ℂ) 1 := by
  rw [mem_ball,dist_zero_right,norm_inv]
  have h : 1 < ‖w‖ := hw
  exact (inv_lt_one₀ (zero_lt_one.trans h)).mpr h

private theorem inv_mem_exterior_of_disk (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) (hz0 : z ≠ 0) :
    z⁻¹ ∈ exteriorDisk := by
  change 1 < ‖z⁻¹‖
  rw [norm_inv]
  exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr (by simpa using hz)

private theorem reciprocalDiskUniformization_ne_zero_of_ne_zero
    {K : Set ℂ} {a : ℂ} (f : ReciprocalDiskUniformization K a)
    (z : ℂ) (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) : f.toFun z ≠ 0 := by
  intro h
  exact hz0 (f.bijective.2.1 hz (mem_ball_self zero_lt_one) (h.trans f.map_zero.symm))

/-- Uniformization at a symmetric reciprocal origin supplies the actual
centered exterior normalization after a nonzero complex dilation. -/
theorem reciprocalDiskUniformization_to_centered_exterior
    (K : Set ℂ) (h0 : (0:ℂ) ∈ continuumFill K) (f : ReciprocalDiskUniformization K 0)
    (hOdd : ∀ z ∈ ball (0:ℂ) 1, f.toFun (-z) = -f.toFun z) :
    ∃ (a : ℂ) (F : ℂ → ℂ), a ≠ 0 ∧ CenteredExteriorUnivalent F ∧
      F '' exteriorDisk = (continuumScale (continuumFill K) a)ᶜ := by
  let a := deriv f.toFun 0
  let F (w : ℂ) := a/(f.toFun w⁻¹)
  have hD : (0:ℂ) ∈ ball (0:ℂ) 1 := mem_ball_self zero_lt_one
  have ha : a ≠ 0 := deriv_ne_zero_of_differentiableOn_injOn isOpen_ball f.differentiable f.bijective.2.1 hD
  have hN (w : ℂ) (hw : w ∈ exteriorDisk) : f.toFun w⁻¹ ≠ 0 :=
    reciprocalDiskUniformization_ne_zero_of_ne_zero f w⁻¹ (inv_mem_disk_of_exterior w hw)
      (inv_ne_zero (exterior_ne_zero hw))
  have hAf (w : ℂ) (hw : w ∈ exteriorDisk) : AnalyticAt ℂ F w := by
    have h := f.differentiable.analyticAt (isOpen_ball.mem_nhds (inv_mem_disk_of_exterior w hw))
    exact analyticAt_const.div (h.comp (f := fun t : ℂ => t⁻¹) (x := w) (analyticAt_inv (exterior_ne_zero hw)))
      (hN w hw)
  have hinj : InjOn F exteriorDisk := by
    intro z hz w hw heq
    change a/f.toFun z⁻¹ = a/f.toFun w⁻¹ at heq
    apply inv_injective
    apply f.bijective.2.1 (inv_mem_disk_of_exterior z hz) (inv_mem_disk_of_exterior w hw)
    apply inv_injective
    exact mul_left_cancel₀ ha (by simpa only [div_eq_mul_inv] using heq)
  let g := dslope f.toFun 0
  have hg0 : g 0 = a := dslope_same _ _
  have hgd : DifferentiableAt ℂ g 0 := by
    have hc : ContinuousAt g 0 := continuousAt_dslope_same.mpr
      (f.differentiable.differentiableAt (ball_mem_nhds _ zero_lt_one))
    have hd : ∀ᶠ t in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one),
        self_mem_nhdsWithin] with t ht ht0
      exact (differentiableAt_dslope_of_ne ht0).mpr
        (f.differentiable.differentiableAt (isOpen_ball.mem_nhds ht))
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc).differentiableAt
  have hEq : (fun t => g (-t)) =ᶠ[𝓝 (0:ℂ)] g := by
    filter_upwards [ball_mem_nhds (0:ℂ) zero_lt_one] with t ht
    by_cases ht0 : t = 0
    · simp [ht0]
    unfold g
    rw [dslope_of_ne f.toFun (neg_ne_zero.mpr ht0),dslope_of_ne f.toFun ht0,
      slope_def_field,slope_def_field,sub_zero,sub_zero,f.map_zero,sub_zero,sub_zero,hOdd t ht,neg_div_neg_eq]
  have hder : HasDerivAt (fun t => g (-t)) (-(deriv g 0)) 0 := by
    have hn : HasDerivAt (fun t : ℂ => -t) (-1) 0 := (hasDerivAt_id (0:ℂ)).neg
    have hg : HasDerivAt g (deriv g 0) (-(0:ℂ)) := by simpa only [neg_zero] using hgd.hasDerivAt
    have h := hg.comp (0:ℂ) hn
    simpa only [Function.comp_def,id_eq,neg_zero,mul_neg_one] using h
  have hd0 : deriv g 0 = 0 := by
    have he := hEq.deriv_eq
    rw [hder.deriv] at he
    linear_combination -he/2
  have hs : Tendsto (slope g 0) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) := by
    simpa only [hd0] using hgd.hasDerivAt.tendsto_slope
  have hgp : Tendsto g (𝓝[≠] (0:ℂ)) (𝓝 a) := by
    rw [←hg0]
    exact hgd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (exteriorForwardGerm F) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) := by
    have hc : Tendsto (fun t => -(slope g 0 t)/g t) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) := by
      simpa only [neg_zero,zero_div,Pi.div_def] using (hs.neg.div hgp ha)
    apply hc.congr'
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one),self_mem_nhdsWithin] with t ht ht0
    have hf0 := reciprocalDiskUniformization_ne_zero_of_ne_zero f t ht ht0
    have hgval : g t = f.toFun t/t := by
      change dslope f.toFun 0 t = _
      rw [dslope_of_ne f.toFun ht0,slope_def_field,f.map_zero,sub_zero,sub_zero]
    rw [exteriorForwardGerm_punctured F ht0]
    change -(slope g 0 t)/g t = a/(f.toFun t⁻¹⁻¹)-t⁻¹
    rw [inv_inv,slope_def_field,hg0,sub_zero,hgval]
    field_simp [show t ≠ 0 from ht0,hf0] <;> ring
  have hc0 : ContinuousAt (exteriorForwardGerm F) 0 :=
    continuousAt_iff_punctured_nhds.mpr (by simpa only [exteriorForwardGerm_zero] using hlim)
  have hdiff : ∀ᶠ t in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ (exteriorForwardGerm F) t := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0:ℂ) zero_lt_one),self_mem_nhdsWithin] with t ht ht0
    have hA : AnalyticAt ℂ (fun u : ℂ => F u⁻¹-u⁻¹) t :=
      ((hAf _ (inv_mem_exterior_of_disk t ht ht0)).comp (f := fun u : ℂ => u⁻¹) (x := t)
        (analyticAt_inv ht0)).sub (analyticAt_inv ht0)
    apply (hA.congr ?_).differentiableAt
    filter_upwards [isOpen_compl_singleton.mem_nhds (show t ∈ ({0}:Set ℂ)ᶜ from ht0)] with u hu
    exact (exteriorForwardGerm_punctured F hu).symm
  have hF : CenteredExteriorUnivalent F := ⟨fun w hw => (hAf w hw).differentiableAt.differentiableWithinAt,hinj,
    Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff hc0⟩
  refine ⟨a,F,ha,hF,?_⟩
  apply Subset.antisymm
  · rintro _ ⟨w,hw,rfl⟩
    have hin := f.bijective.1 (inv_mem_disk_of_exterior w hw)
    have hout := (mem_reciprocalExteriorDomain_iff K 0 _ (hN w hw)).mp hin
    rw [zero_add] at hout
    rintro ⟨z,hz,he⟩
    change a*z = a/(f.toFun w⁻¹) at he
    rw [div_eq_mul_inv] at he
    exact hout ((mul_left_cancel₀ ha he) ▸ hz)
  · intro z hz
    let y := z/a
    have hy : y ∉ continuumFill K := fun h => hz ⟨y,h,by dsimp [y]; field_simp [ha]⟩
    have hy0 : y ≠ 0 := fun h => hy (h.symm ▸ h0)
    have hyU : y⁻¹ ∈ reciprocalExteriorDomain K 0 := by
      apply (mem_reciprocalExteriorDomain_iff K 0 _ (inv_ne_zero hy0)).mpr
      rwa [inv_inv,zero_add]
    obtain ⟨t,ht,hyt⟩ := f.bijective.2.2 hyU
    have ht0 : t ≠ 0 := fun h => inv_ne_zero hy0 (by rw [←hyt,h,f.map_zero])
    refine ⟨t⁻¹,inv_mem_exterior_of_disk t ht ht0,?_⟩
    change a/f.toFun t⁻¹⁻¹ = z
    rw [inv_inv,hyt,div_eq_mul_inv,inv_inv]
    dsimp [y]
    field_simp [ha]

end SpringerLean
