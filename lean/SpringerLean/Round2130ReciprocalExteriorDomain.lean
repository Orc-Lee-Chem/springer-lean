import SpringerLean.Round2103FilledRotationalSymmetry

open Set Metric Filter Bornology
open scoped Topology

namespace SpringerLean

/-- The reciprocal coordinate centered at an omitted point and filled
in at the image of infinity. -/
def reciprocalExteriorDomain (K : Set ℂ) (a : ℂ) : Set ℂ :=
  insert 0 ((fun z : ℂ => (z-a)⁻¹) '' (continuumFill K)ᶜ)

theorem mem_reciprocalExteriorDomain_iff
    (K : Set ℂ) (a z : ℂ) (hz : z ≠ 0) :
    z ∈ reciprocalExteriorDomain K a ↔ a+z⁻¹ ∈ (continuumFill K)ᶜ := by
  change z ∈ insert 0 ((fun w : ℂ => (w-a)⁻¹) '' (continuumFill K)ᶜ) ↔ _
  rw [mem_insert_iff,or_iff_right hz]
  constructor
  · rintro ⟨w,hw,he⟩
    have h : a+z⁻¹=w := by rw [←he,inv_inv]; ring
    rwa [h]
  · intro h
    refine ⟨a+z⁻¹,h,?_⟩
    change (a+z⁻¹-a)⁻¹ = z
    rw [show a+z⁻¹-a=z⁻¹ by ring,inv_inv]

theorem reciprocalExteriorDomain_isOpen
    (K : Set ℂ) (hK : IsCompact K) (a : ℂ) : IsOpen (reciprocalExteriorDomain K a) := by
  let U := reciprocalExteriorDomain K a
  let L := continuumFill K
  have hO := (isClosed_continuumFill K hK.isClosed).isOpen_compl
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    obtain ⟨M,hM⟩ := (isBounded_continuumFill K hK).exists_norm_le
    let R := max (M+‖a‖) 1 + 1
    have hR : 0 < R := by dsimp [R]; linarith [le_max_right (M+‖a‖) (1:ℝ)]
    refine (Metric.mem_nhds_iff.mpr ⟨R⁻¹,inv_pos.mpr hR,?_⟩)
    intro z hz
    by_cases hz0 : z = 0
    · subst z; exact mem_insert _ _
    apply (mem_reciprocalExteriorDomain_iff K a z hz0).mpr
    intro h
    have hM' := hM _ h
    have hnorm : ‖z‖ < R⁻¹ := by simpa only [mem_ball,dist_zero_right] using hz
    have hlarge : R < ‖z‖⁻¹ := (lt_inv_comm₀ hR (norm_pos_iff.mpr hz0)).mpr hnorm
    have hn : ‖z‖⁻¹ ≤ ‖a+z⁻¹‖+‖a‖ := by
      simpa only [show (a+z⁻¹)-a=z⁻¹ by ring,norm_inv] using norm_sub_le (a+z⁻¹) a
    have hle : M+‖a‖ ≤ max (M+‖a‖) 1 := le_max_left _ _
    dsimp [R] at hlarge
    linarith only [hlarge,hn,hM',hle]
  · have hin := (mem_reciprocalExteriorDomain_iff K a z hz0).mp hz
    have hc : ContinuousAt (fun w : ℂ => a+w⁻¹) z := continuousAt_const.add (continuousAt_inv₀ hz0)
    have he : ∀ᶠ w in 𝓝 z, a+w⁻¹ ∈ Lᶜ := hc.eventually (hO.mem_nhds hin)
    have hs : {w : ℂ | w ≠ 0} ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds hz0
    filter_upwards [he,hs] with w hw hw0
    exact (mem_reciprocalExteriorDomain_iff K a w hw0).mpr hw

theorem reciprocalExteriorDomain_isConnected
    (K : Set ℂ) (hK : IsCompact K) (a : ℂ) (ha : a ∈ continuumFill K) :
    IsConnected (reciprocalExteriorDomain K a) := by
  let U := reciprocalExteriorDomain K a
  let f (z : ℂ) := (z-a)⁻¹
  let O := (continuumFill K)ᶜ
  let V := f '' O
  have hO := continuumFill_compl_isConnected K hK
  have hf : ContinuousOn f O := by
    apply (continuous_id.sub continuous_const).continuousOn.inv₀
    intro z hz
    apply sub_ne_zero.mpr
    intro h
    change z = a at h
    exact hz (by rwa [h])
  have hV : IsConnected V := hO.image f hf
  have ho : IsOpen U := reciprocalExteriorDomain_isOpen K hK a
  have hu0 : (0:ℂ) ∈ U := mem_insert _ _
  obtain ⟨δ,hδ,hδU⟩ := Metric.isOpen_iff.mp ho 0 hu0
  have hc : (0:ℂ) ∈ closure V := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r := min ε δ/2
    have hr : 0 < r := half_pos (lt_min hε hδ)
    let z : ℂ := (r:ℂ)
    have hn : ‖z‖ = r := by rw [show z = (r:ℂ) from rfl,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hn ▸ hr.ne')
    have hzU : z ∈ U := hδU (by
      rw [mem_ball,dist_zero_right,hn]
      exact (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _))
    have hzV : z ∈ V := (mem_insert_iff.mp hzU).resolve_left hz0
    refine ⟨z,hzV,?_⟩
    rw [dist_comm,dist_zero_right,hn]
    exact (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hU : U ⊆ closure V := by
    intro z hz
    rcases mem_insert_iff.mp hz with he | he
    · exact he.symm ▸ hc
    · exact subset_closure he
  exact hV.subset_closure (subset_insert _ _) hU

theorem reciprocalExteriorDomain_ne_univ
    (K : Set ℂ) (a b : ℂ) (hb : b ∈ continuumFill K) (hab : a ≠ b) :
    reciprocalExteriorDomain K a ≠ univ := by
  intro h
  have hz : (b-a)⁻¹ ∈ reciprocalExteriorDomain K a := h.symm ▸ mem_univ _
  have h' := (mem_reciprocalExteriorDomain_iff K a _ (inv_ne_zero (sub_ne_zero.mpr hab.symm))).mp hz
  rw [inv_inv,show a+(b-a)=b by ring] at h'
  exact h' hb

end SpringerLean
