import SpringerLean.Round2028TransitionGerm

open scoped Topology

namespace SpringerLean

theorem exteriorInverse_analyticAt_image
    (G : ℂ → ℂ) (hc : CenteredExteriorUnivalent G)
    (v : ℂ) (hv : v ∈ exteriorDisk) :
    AnalyticAt ℂ (exteriorInverse G) (G v) := by
  have hGa : AnalyticAt ℂ G v :=
    hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hv)
  have hd : deriv G v ≠ 0 :=
    deriv_ne_zero_of_differentiableOn_injOn
      exteriorDisk_isOpen hc.1 hc.2.1 hv
  let R : ℂ → ℂ :=
    hGa.hasStrictDerivAt.localInverse G (deriv G v) v hd
  have hR0 : R (G v) = v :=
    HasStrictFDerivAt.localInverse_apply_image
      (hGa.hasStrictDerivAt.hasStrictFDerivAt_equiv hd)
  have hRa : AnalyticAt ℂ R (G v) :=
    hGa.analyticAt_localInverse hd
  have hRin : ∀ᶠ u in 𝓝 (G v), R u ∈ exteriorDisk := by
    apply hRa.continuousAt.eventually
    rw [hR0]
    exact exteriorDisk_isOpen.mem_nhds hv
  have hright : ∀ᶠ u in 𝓝 (G v), G (R u) = u :=
    hGa.hasStrictDerivAt.eventually_right_inverse hd
  have hEq : R =ᶠ[𝓝 (G v)] exteriorInverse G := by
    filter_upwards [hRin, hright] with u hu hGu
    have hImage : u ∈ G '' exteriorDisk := ⟨R u, hu, hGu⟩
    have hInvMem : exteriorInverse G u ∈ exteriorDisk :=
      Function.invFunOn_mem hImage
    have hInvEq : G (exteriorInverse G u) = u :=
      Function.invFunOn_eq hImage
    exact hc.2.1 hu hInvMem (hGu.trans hInvEq.symm)
  exact hRa.congr hEq

theorem exteriorTransitionDisk_analyticAt_nonzero
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G)
    (hImage : F '' exteriorDisk = G '' exteriorDisk)
    (t : ℂ) (ht : t ∈ Metric.ball (0:ℂ) 1) (ht0 : t ≠ 0) :
    AnalyticAt ℂ (exteriorTransitionDisk F G) t := by
  have htnorm : ‖t‖ < 1 := by simpa using ht
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have htinv : t⁻¹ ∈ exteriorDisk := by
    change 1 < ‖t⁻¹‖
    rw [norm_inv]
    have h := one_div_lt_one_div_of_lt htpos htnorm
    simpa [one_div] using h
  have hImagePt : F t⁻¹ ∈ G '' exteriorDisk := by
    rw [← hImage]
    exact ⟨t⁻¹, htinv, rfl⟩
  let v := exteriorInverse G (F t⁻¹)
  have hv : v ∈ exteriorDisk := Function.invFunOn_mem hImagePt
  have hGv : G v = F t⁻¹ := Function.invFunOn_eq hImagePt
  have hInvGa : AnalyticAt ℂ (exteriorInverse G) (F t⁻¹) := by
    rw [← hGv]
    exact exteriorInverse_analyticAt_image G hG v hv
  have hTa : AnalyticAt ℂ (fun s : ℂ => s⁻¹) t := analyticAt_inv ht0
  have hFa : AnalyticAt ℂ (fun s : ℂ => F s⁻¹) t := by
    have hh : AnalyticAt ℂ F ((fun s : ℂ => s⁻¹) t) := by
      exact hF.1.analyticAt (exteriorDisk_isOpen.mem_nhds htinv)
    exact hh.comp hTa
  have hComp : AnalyticAt ℂ
      (fun s : ℂ => exteriorInverse G (F s⁻¹)) t := by
    have hh : AnalyticAt ℂ (exteriorInverse G)
        ((fun s : ℂ => F s⁻¹) t) := by simpa using hInvGa
    exact AnalyticAt.comp (f := fun s : ℂ => F s⁻¹) hh hFa
  have hv0 : v ≠ 0 := by
    intro heq
    simp [heq, exteriorDisk] at hv
    norm_num at hv
  have hRecip : AnalyticAt ℂ
      (fun s : ℂ => (exteriorInverse G (F s⁻¹))⁻¹) t :=
    hComp.inv hv0
  have hEq : (fun s : ℂ => (exteriorInverse G (F s⁻¹))⁻¹) =ᶠ[𝓝 t]
      exteriorTransitionDisk F G := by
    filter_upwards [continuousAt_id.eventually_ne ht0] with s hs
    have hs0 : s ≠ 0 := by simpa only [id_eq] using hs
    simp [exteriorTransitionDisk, hs0]
  exact hRecip.congr hEq

theorem exteriorTransitionDisk_differentiableOn_unitDisk
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G)
    (hImage : F '' exteriorDisk = G '' exteriorDisk) :
    DifferentiableOn ℂ (exteriorTransitionDisk F G)
      (Metric.ball (0:ℂ) 1) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact (exteriorTransitionDisk_analyticAt_zero F G hF hG hImage).differentiableAt.differentiableWithinAt
  · exact (exteriorTransitionDisk_analyticAt_nonzero F G hF hG hImage t ht ht0).differentiableAt.differentiableWithinAt

theorem centeredExteriorUnivalent_eqOn_of_same_image
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (hG : CenteredExteriorUnivalent G)
    (hImage : F '' exteriorDisk = G '' exteriorDisk) :
    Set.EqOn F G exteriorDisk := by
  have hDisk : Set.EqOn (exteriorTransitionDisk F G) id
      (Metric.ball (0:ℂ) 1) :=
    unitDisk_selfMap_deriv_one_eq_id
      (exteriorTransitionDisk F G)
      (exteriorTransitionDisk_differentiableOn_unitDisk F G hF hG hImage)
      (fun t ht => exteriorTransitionDisk_mem_ball F G hImage t ht)
      (exteriorTransitionDisk_zero F G)
      (exteriorTransitionDisk_hasDerivAt_zero F G hF hG hImage).deriv
  intro z hz
  let t : ℂ := z⁻¹
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq, exteriorDisk] at hz
    norm_num at hz
  have ht0 : t ≠ 0 := inv_ne_zero hz0
  have htnorm : ‖t‖ < 1 := by
    change ‖z⁻¹‖ < 1
    rw [norm_inv]
    have hh := one_div_lt_one_div_of_lt
      (by norm_num : (0:ℝ)<1) hz
    simpa [one_div] using hh
  have ht : t ∈ Metric.ball (0:ℂ) 1 := by simpa using htnorm
  have hEq : exteriorTransitionDisk F G t = t := by
    simpa only [id_eq] using hDisk ht
  have hFunc := exteriorTransitionDisk_functional F G hImage t ht ht0
  rw [hEq] at hFunc
  simpa [t] using hFunc.symm

theorem normalizedExteriorMapUnique_actual
    (F : ℂ → ℂ) (K : Set ℂ)
    (hF : CenteredExteriorUnivalent F)
    (hImage : F '' exteriorDisk = Kᶜ) :
    NormalizedExteriorMapUnique F K := by
  intro G hG hGImage
  exact centeredExteriorUnivalent_eqOn_of_same_image G F hG hF
    (hGImage.trans hImage.symm)

theorem evenExteriorCovariant_actual
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    EvenExteriorCovariant F k :=
  evenExteriorCovariant_of_map_unique F K k hk hF
    (evenGeneratorInvariant_to_evenRotationInvariant K k hk hK)
    hImage (normalizedExteriorMapUnique_actual F K hF hImage)

end SpringerLean

#print axioms SpringerLean.exteriorInverse_analyticAt_image
#print axioms SpringerLean.exteriorTransitionDisk_differentiableOn_unitDisk
#print axioms SpringerLean.centeredExteriorUnivalent_eqOn_of_same_image
#print axioms SpringerLean.normalizedExteriorMapUnique_actual
#print axioms SpringerLean.evenExteriorCovariant_actual
