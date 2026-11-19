import SpringerLean.Round2131ReciprocalDiskUniformization

open Set Metric Function

namespace SpringerLean

noncomputable def reciprocalRotation (a η : ℂ) (z : ℂ) : ℂ :=
  z/(η+(η-1)*a*z)

theorem reciprocalRotation_zero (a η : ℂ) : reciprocalRotation a η 0 = 0 := by
  simp [reciprocalRotation]

theorem reciprocalRotation_den_ne_zero
    (K : Set ℂ) (a η z : ℂ) (ha : a ∈ continuumFill K) (hη : η ≠ 0)
    (hrot : ∀ w : ℂ, η*w ∈ continuumFill K ↔ w ∈ continuumFill K)
    (hz : z ∈ reciprocalExteriorDomain K a) : η+(η-1)*a*z ≠ 0 := by
  by_cases h0 : z = 0
  · simpa [h0] using hη
  have h := (mem_reciprocalExteriorDomain_iff K a z h0).mp hz
  have hd : η*(a+z⁻¹)-a ≠ 0 := by
    intro hd
    have he := sub_eq_zero.mp hd
    exact h ((hrot _).mp (he.symm ▸ ha))
  have he : η+(η-1)*a*z = (η*(a+z⁻¹)-a)*z := by
    field_simp [h0]
    ring
  rw [he]
  exact mul_ne_zero hd h0

theorem reciprocalRotation_physical
    (a η z : ℂ) (hz0 : z ≠ 0) : a+(reciprocalRotation a η z)⁻¹ = η*(a+z⁻¹) := by
  rw [reciprocalRotation,inv_div]
  field_simp [hz0]
  ring

theorem reciprocalRotation_mapsTo
    (K : Set ℂ) (a η : ℂ) (ha : a ∈ continuumFill K) (hη : η ≠ 0)
    (hrot : ∀ w : ℂ, η*w ∈ continuumFill K ↔ w ∈ continuumFill K) :
    MapsTo (reciprocalRotation a η) (reciprocalExteriorDomain K a) (reciprocalExteriorDomain K a) := by
  intro z hz
  by_cases h0 : z = 0
  · rw [h0,reciprocalRotation_zero]; exact mem_insert _ _
  have hd := reciprocalRotation_den_ne_zero K a η z ha hη hrot hz
  have hne : reciprocalRotation a η z ≠ 0 := div_ne_zero h0 hd
  apply (mem_reciprocalExteriorDomain_iff K a _ hne).mpr
  rw [reciprocalRotation_physical a η z h0]
  exact fun h => (mem_reciprocalExteriorDomain_iff K a z h0).mp hz ((hrot _).mp h)

theorem reciprocalRotation_differentiableOn
    (K : Set ℂ) (a η : ℂ) (ha : a ∈ continuumFill K) (hη : η ≠ 0)
    (hrot : ∀ w : ℂ, η*w ∈ continuumFill K ↔ w ∈ continuumFill K) :
    DifferentiableOn ℂ (reciprocalRotation a η) (reciprocalExteriorDomain K a) := by
  unfold reciprocalRotation
  exact differentiableOn_id.div (by fun_prop)
    (fun z hz => reciprocalRotation_den_ne_zero K a η z ha hη hrot hz)

/-- Once the reciprocal disk uniformization is supplied, a nontrivial
rotation cannot fix a second exterior point. Hence its center belongs
to the filled set. This does not presume the exterior normalization. -/
theorem zero_mem_continuumFill_of_reciprocalDiskUniformization
    (K : Set ℂ) (hK : IsCompact K) (a η : ℂ) (ha : a ∈ continuumFill K)
    (hη0 : η ≠ 0) (hη1 : η ≠ 1)
    (hrot : ∀ w : ℂ, η*w ∈ continuumFill K ↔ w ∈ continuumFill K)
    (f : ReciprocalDiskUniformization K a) : (0:ℂ) ∈ continuumFill K := by
  by_contra hn
  let U := reciprocalExteriorDomain K a
  let D := ball (0:ℂ) 1
  let g := invFunOn f.toFun D
  let T := reciprocalRotation a η
  let A := g ∘ T ∘ f.toFun
  have hU : f.toFun '' D = U := f.bijective.image_eq
  have hG : MapsTo g U D := fun w hw =>
    invFunOn_mem (show w ∈ f.toFun '' D by rwa [hU])
  have hD : MapsTo A D D := hG.comp ((reciprocalRotation_mapsTo K a η ha hη0 hrot).comp f.bijective.1)
  have hgd : DifferentiableOn ℂ g U := fun z hz =>
    (reciprocalDiskUniformization_inverse_analyticAt f z hz).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ A D := hgd.comp
    ((reciprocalRotation_differentiableOn K a η ha hη0 hrot).comp f.differentiable f.bijective.1)
    ((reciprocalRotation_mapsTo K a η ha hη0 hrot).comp f.bijective.1)
  have h0D : (0:ℂ) ∈ D := mem_ball_self zero_lt_one
  have hG0 : g 0 = 0 := by
    have h := f.bijective.2.1.leftInvOn_invFunOn h0D
    simpa only [f.map_zero] using h
  have hA0 : A 0 = 0 := by simp only [A,Function.comp_apply,f.map_zero,T,reciprocalRotation_zero,hG0]
  have ha0 : a ≠ 0 := fun h => hn (h ▸ ha)
  let q := (-a)⁻¹
  have hq0 : q ≠ 0 := inv_ne_zero (neg_ne_zero.mpr ha0)
  have hphys0 : a+q⁻¹ = 0 := by simp [q]
  have hq : q ∈ U := (mem_reciprocalExteriorDomain_iff K a q hq0).mpr (hphys0.symm ▸ hn)
  have hTq : T q = q := by
    apply inv_injective
    have h := reciprocalRotation_physical a η q hq0
    rw [hphys0,mul_zero] at h
    exact add_left_cancel (h.trans hphys0.symm)
  obtain ⟨z,hz,hzq⟩ := f.bijective.2.2 hq
  have hz0 : z ≠ 0 := fun h => hq0 (by rw [←hzq,h,f.map_zero])
  have hfix : A z = z := by
    change g (T (f.toFun z)) = z
    rw [hzq,hTq,←hzq]
    exact f.bijective.2.1.leftInvOn_invFunOn hz
  have hAid := holomorphic_disk_selfMap_eq_id_of_nonzero_fixed_point A hd hD hA0 z hz hz0 hfix
  have hTid : EqOn T id U := by
    intro p hp
    obtain ⟨w,hw,hw'⟩ := f.bijective.2.2 hp
    have he : g (T p) = w := by
      rw [←hw']
      exact hAid hw
    have hTp : T p ∈ U := reciprocalRotation_mapsTo K a η ha hη0 hrot hp
    have hh := invFunOn_eq (f := f.toFun) (s := D) (hU.symm ▸ hTp)
    change f.toFun (g (T p)) = T p at hh
    rw [he,hw'] at hh
    exact hh.symm
  obtain ⟨B,hB⟩ := (isBounded_continuumFill K hK).exists_norm_le
  let w : ℂ := (max B 0 + 1 : ℝ)
  have hn' : 0 < max B 0+1 := by positivity
  have hw : ‖w‖ = max B 0+1 := by
    change ‖((max B 0+1:ℝ):ℂ)‖ = _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn']
  have hw0 : w ≠ 0 := norm_ne_zero_iff.mp (hw ▸ hn'.ne')
  have hwK : w ∉ continuumFill K := by
    intro hm
    have h := hB w hm
    rw [hw] at h
    linarith [le_max_left B 0]
  let p := (w-a)⁻¹
  have hp0 : p ≠ 0 := inv_ne_zero (sub_ne_zero.mpr fun h => hwK (h.symm ▸ ha))
  have hphys : a+p⁻¹ = w := by dsimp [p]; rw [inv_inv]; ring
  have hp : p ∈ U := (mem_reciprocalExteriorDomain_iff K a p hp0).mpr (hphys.symm ▸ hwK)
  have h := reciprocalRotation_physical a η p hp0
  change a+(T p)⁻¹ = η*(a+p⁻¹) at h
  have he : T p = p := hTid hp
  rw [he,hphys] at h
  have hη : η = 1 := mul_right_cancel₀ hw0 (by simpa only [one_mul] using h.symm)
  exact hη1 hη

end SpringerLean
