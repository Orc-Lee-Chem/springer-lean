import SpringerLean.Round2103FilledRotationalSymmetry
import SpringerLean.Round1950RegularStarRays
import Mathlib.Analysis.Complex.OpenMapping

open Set Metric

namespace SpringerLean

theorem regularStarRaySet_interior_empty (m : ℕ) (hm : 0 < m) :
    interior (regularStarRaySet m) = ∅ := by
  let S := regularStarRaySet m
  let f (z : ℂ) := z^m
  have hf : AnalyticOnNhd ℂ f univ := by intro z _; unfold f; fun_prop
  have ho : IsOpenMap f := hf.is_constant_or_isOpenMap.resolve_left (by
    rintro ⟨c,hc⟩
    have h0 : f 0 = 0 := by simp [f,zero_pow hm.ne']
    have h1 : f 1 = 1 := by simp [f]
    have he : (1:ℂ) = 0 := h1.symm.trans ((hc 1).trans ((hc 0).symm.trans h0))
    exact one_ne_zero he)
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hne
  obtain ⟨w,hw⟩ := hne.image f
  have hOpen := ho (interior S) isOpen_interior
  have hline : ∀ z ∈ f '' interior S, z.im = 0 := by
    rintro _ ⟨z,hz,rfl⟩
    have h : z ∈ regularStarRaySet m := interior_subset hz
    rw [←regularStarPowerSet_eq_raySet m hm] at h
    exact h.1
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hOpen w hw
  let v := w+((r/2:ℝ):ℂ)*Complex.I
  have hv : v ∈ ball w r := by
    rw [mem_ball,dist_eq_norm,show v-w = ((r/2:ℝ):ℂ)*Complex.I by dsimp [v]; ring,
      norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
    linarith
  have hv0 := hline v (hball hv)
  have he : v.im = r/2 := by simp [v,Complex.add_im,Complex.mul_im,hline w hw]
  linarith

theorem regularStarRaySet_scale_interior_empty (m : ℕ) (hm : 0 < m) (b : ℂ) (hb : b ≠ 0) :
    interior ((fun z : ℂ => b*z) '' regularStarRaySet m) = ∅ := by
  let A := interior ((fun z : ℂ => b*z) '' regularStarRaySet m)
  let f (z : ℂ) := b*z
  let U := f ⁻¹' A
  have hUc : IsOpen U := isOpen_interior.preimage (by unfold f; fun_prop)
  have hU : U ⊆ regularStarRaySet m := by
    intro z hz
    obtain ⟨w,hw,hwz⟩ := interior_subset (show f z ∈ A from hz)
    have he : w = z := mul_left_cancel₀ hb hwz
    exact he ▸ hw
  have hE : U = ∅ := by
    apply Set.subset_empty_iff.mp
    rw [←regularStarRaySet_interior_empty m hm]
    exact interior_maximal hU hUc
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨z,hz⟩
  obtain ⟨w,_,he⟩ := interior_subset (show z ∈ A from hz)
  have hw : w ∈ U := by
    change b*w ∈ A
    rw [show b*w = z from he]
    exact hz
  rw [hE] at hw
  exact hw.elim

end SpringerLean
