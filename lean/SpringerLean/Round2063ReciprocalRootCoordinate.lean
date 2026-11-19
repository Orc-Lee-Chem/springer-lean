import SpringerLean.Round2061PolynomialExteriorTopology
import SpringerLean.Round2062ReciprocalLogExhaustion

open Polynomial Set Metric Filter
open scoped Topology

namespace SpringerLean

theorem mem_reciprocalSeparation_zero_iff
    (K : Set ℂ) {u : ℂ} (hu : u ≠ 0) :
    u ∈ reciprocalSeparation K 0 ↔ u⁻¹ ∉ K := by
  constructor
  · intro h hm
    have hp := h u⁻¹ hm
    simp [hu] at hp
  · intro h a ha
    have hne : 1-a*u ≠ 0 := by
      intro heq
      apply h
      have hp : a*u=1 := by linear_combination -heq
      have ha' : a = u⁻¹ := by
        field_simp [hu]
        exact hp
      exact ha' ▸ ha
    simpa only [zero_mul] using norm_pos_iff.mpr hne

/-- If zero lies in the compact set and its complement is connected,
the reciprocal domain, including reciprocal infinity, is connected. -/
theorem reciprocalSeparation_zero_isConnected
    (K : Set ℂ) (hK : IsCompact K) (h0 : (0 : ℂ) ∈ K) (hc : IsConnected Kᶜ) :
    IsConnected (reciprocalSeparation K 0) := by
  let E := Inv.inv '' Kᶜ
  have hE : IsConnected E := hc.image _ (continuousOn_inv₀.mono (by
    intro z hz hzero
    exact hz (hzero ▸ h0)))
  have hins : reciprocalSeparation K 0 = insert 0 E := by
    ext u
    by_cases hu : u = 0
    · subst u
      simp only [zero_mem_reciprocalSeparation, mem_insert_iff, true_or]
    · rw [mem_reciprocalSeparation_zero_iff K hu, mem_insert_iff]
      simp only [hu, false_or]
      constructor
      · intro h
        exact ⟨u⁻¹, h, inv_inv _⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
  have hcl : (0 : ℂ) ∈ closure E := by
    have hh : ∀ᶠ u : ℂ in 𝓝[≠] (0 : ℂ), u ∈ E := by
      have hnear : reciprocalSeparation K 0 ∈ 𝓝[≠] (0 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds
          ((reciprocalSeparation_isOpen K hK 0).mem_nhds (zero_mem_reciprocalSeparation K 0))
      filter_upwards [self_mem_nhdsWithin,
        hnear] with u hne hU
      exact ⟨u⁻¹, (mem_reciprocalSeparation_zero_iff K hne).mp hU, inv_inv _⟩
    exact mem_closure_of_tendsto (tendsto_id.mono_left nhdsWithin_le_nhds) hh
  rw [hins]
  exact hE.subset_closure (subset_insert _ _) (insert_subset hcl subset_closure)

theorem translated_lemniscate_reciprocal_properties
    (Q : ℂ[X]) (hQ : 0 < Q.natDegree)
    (hconn : IsConnected {z : ℂ | ‖Q.eval z‖ ≤ 1})
    (b : ℂ) (hb : ‖Q.eval b‖ ≤ 1) :
    let K := (fun z : ℂ => z-b) '' {z : ℂ | ‖Q.eval z‖ ≤ 1}
    IsCompact K ∧ IsConnected K ∧ (0 : ℂ) ∈ K ∧
      IsConnected (reciprocalSeparation K 0) := by
  let K := (fun z : ℂ => z-b) '' {z : ℂ | ‖Q.eval z‖ ≤ 1}
  have hcont : Continuous (fun z : ℂ => z-b) := continuous_id.sub continuous_const
  have hK : IsCompact K := (polynomial_unit_lemniscate_isCompact Q hQ).image hcont
  have hC : IsConnected K := hconn.image _ hcont.continuousOn
  have hzero : (0 : ℂ) ∈ K := ⟨b, hb, sub_self b⟩
  have heq : Kᶜ = (fun z : ℂ => z-b) '' {z : ℂ | 1 < ‖Q.eval z‖} := by
    ext w
    constructor
    · intro hw
      refine ⟨w+b, ?_, by ring⟩
      change 1 < ‖Q.eval (w+b)‖
      by_contra! hn
      apply hw
      exact ⟨w+b, hn, by ring⟩
    · rintro ⟨z, hz, rfl⟩ ⟨x, hx, heq⟩
      have h : x = z := by linear_combination heq
      subst x
      change ‖Q.eval z‖ ≤ 1 at hx
      change 1 < ‖Q.eval z‖ at hz
      exact (not_lt_of_ge hx) hz
  have hc : IsConnected Kᶜ := by
    rw [heq]
    exact (polynomial_unit_lemniscate_exterior_isConnected Q hQ).image _ hcont.continuousOn
  exact ⟨hK, hC, hzero, reciprocalSeparation_zero_isConnected K hK hzero hc⟩

end SpringerLean
