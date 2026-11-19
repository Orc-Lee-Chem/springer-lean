import SpringerLean.Round2130ReciprocalExteriorDomain
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

open Set Filter Bornology
open scoped Topology OnePoint

namespace SpringerLean

private noncomputable def reciprocalPlaneToSphere (a z : ℂ) : OnePoint ℂ :=
  if z = a then ∞ else ((z-a)⁻¹ : ℂ)

private theorem continuous_reciprocalPlaneToSphere (a : ℂ) :
    Continuous (reciprocalPlaneToSphere a) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases h : z = a
  · subst z
    rw [continuousAt_iff_punctured_nhds]
    have hs : Tendsto (fun z : ℂ => z-a) (𝓝[≠] a) (𝓝[≠] (0:ℂ)) := by
      refine tendsto_inf.mpr ⟨?_,?_⟩
      · have hs' := (continuous_id.sub continuous_const :
            Continuous (fun z : ℂ => z-a)).continuousAt (x := a)
        have hsub : a-a = (0:ℂ) := sub_self _
        have hs'' : Tendsto (fun w : ℂ => w-a) (𝓝 a) (𝓝 (a-a)) := hs'.tendsto
        rw [hsub] at hs''
        exact hs''.mono_left nhdsWithin_le_nhds
      · apply tendsto_principal.mpr
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact sub_ne_zero.mpr hz
    have hi : Tendsto ((↑) : ℂ → OnePoint ℂ) (cobounded ℂ) (𝓝 ∞) := by
      rw [Metric.cobounded_eq_cocompact,←coclosedCompact_eq_cocompact]
      exact OnePoint.tendsto_coe_infty
    rw [reciprocalPlaneToSphere,if_pos rfl]
    apply (hi.comp (tendsto_inv₀_nhdsNE_zero.comp hs)).congr'
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Function.comp_apply,reciprocalPlaneToSphere,if_neg (show w ≠ a from hw)]
  · have hc : ContinuousAt (fun w : ℂ => (w-a)⁻¹) z :=
      (continuous_id.sub continuous_const).continuousAt.inv₀ (sub_ne_zero.mpr h)
    apply (OnePoint.continuous_coe.continuousAt.comp hc).congr
    filter_upwards [isOpen_compl_singleton.mem_nhds h] with w hw
    simp only [Function.comp_apply,reciprocalPlaneToSphere,if_neg (show w ≠ a from hw)]

/-- The reciprocal domain has connected complement in the one-point
compactification. The base point of the physical filling maps to
infinity. -/
theorem reciprocalExteriorDomain_sphere_compl_isConnected
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K)
    (a : ℂ) (ha : a ∈ continuumFill K) :
    IsConnected (((↑) : ℂ → OnePoint ℂ) '' reciprocalExteriorDomain K a)ᶜ := by
  let C := continuumFill K
  let U := reciprocalExteriorDomain K a
  have hIm : reciprocalPlaneToSphere a '' C = (((↑) : ℂ → OnePoint ℂ) '' U)ᶜ := by
    rw [OnePoint.compl_image_coe]
    apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      by_cases h : z = a
      · simp only [reciprocalPlaneToSphere,h,if_pos,mem_union,mem_singleton_iff,or_true]
      · left
        refine ⟨(z-a)⁻¹,?_,by simp [reciprocalPlaneToSphere,h]⟩
        rw [mem_compl_iff,mem_reciprocalExteriorDomain_iff K a _ (inv_ne_zero (sub_ne_zero.mpr h)),
          inv_inv,show a+(z-a)=z by ring]
        exact not_not_intro hz
    · rintro w (⟨z,hz,rfl⟩ | hw)
      · have hz0 : z ≠ 0 := fun h => hz (h.symm ▸ mem_insert _ _)
        have hza : a+z⁻¹ ≠ a := fun h =>
          inv_ne_zero hz0 (add_left_cancel (h.trans (add_zero a).symm))
        have hzC : a+z⁻¹ ∈ C := by
          rw [mem_compl_iff,mem_reciprocalExteriorDomain_iff K a z hz0,mem_compl_iff,not_not] at hz
          exact hz
        refine ⟨a+z⁻¹,hzC,?_⟩
        rw [reciprocalPlaneToSphere,if_neg hza,show a+z⁻¹-a=z⁻¹ by ring,inv_inv]
      · have he : w = ∞ := hw
        exact ⟨a,ha,by simp [reciprocalPlaneToSphere,he]⟩
  rw [←hIm]
  exact (continuumFill_isConnected K hK.isClosed hc).image _ (continuous_reciprocalPlaneToSphere a).continuousOn

end SpringerLean
