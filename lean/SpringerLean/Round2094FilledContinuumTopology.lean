import SpringerLean.Round2093PolynomialNormFilling

open Set Metric Bornology

namespace SpringerLean

/-- Every point added by filling has a neighborhood contained in the
filled set. In particular a filling with empty interior adds no points. -/
theorem continuumFill_diff_subset_interior (K : Set ℂ) (hK : IsClosed K) :
    continuumFill K \ K ⊆ interior (continuumFill K) := by
  intro z hz
  have hb : IsBounded (connectedComponentIn Kᶜ z) := hz.1.resolve_left hz.2
  have hin : connectedComponentIn Kᶜ z ⊆ continuumFill K := by
    intro w hw
    apply Or.inr
    change IsBounded (connectedComponentIn Kᶜ w)
    rwa [← connectedComponentIn_eq hw]
  exact (interior_maximal hin hK.isOpen_compl.connectedComponentIn) (mem_connectedComponentIn hz.2)

/-- Filling preserves connectedness because every added component has
a boundary point on the original continuum. -/
theorem continuumFill_isConnected (K : Set ℂ) (hK : IsClosed K) (hc : IsConnected K) :
    IsConnected (continuumFill K) := by
  obtain ⟨a,ha⟩ := hc.nonempty
  let W (z : continuumFill K) := K ∪ closure (connectedComponentIn Kᶜ (z:ℂ))
  have hwsub (z : continuumFill K) : W z ⊆ continuumFill K := by
    intro w hw
    rcases hw with hw | hw
    · exact Or.inl hw
    by_cases hz : (z:ℂ) ∈ K
    · rw [connectedComponentIn_eq_empty (show (z:ℂ) ∉ Kᶜ from fun h => h hz), closure_empty] at hw
      exact hw.elim
    · have hb : IsBounded (connectedComponentIn Kᶜ (z:ℂ)) := z.2.resolve_left hz
      rw [closure_eq_self_union_frontier] at hw
      rcases hw with hw | hw
      · apply Or.inr
        change IsBounded (connectedComponentIn Kᶜ w)
        rwa [← connectedComponentIn_eq hw]
      · exact Or.inl (frontier_complementary_component_subset K hK _ hw)
  have hW : continuumFill K = ⋃ z : continuumFill K, W z := by
    apply Subset.antisymm
    · intro z hz
      apply mem_iUnion.mpr
      refine ⟨⟨z,hz⟩,?_⟩
      by_cases hzK : z ∈ K
      · exact Or.inl hzK
      · exact Or.inr (subset_closure (mem_connectedComponentIn hzK))
    · exact iUnion_subset hwsub
  refine ⟨⟨a,Or.inl ha⟩,?_⟩
  rw [hW]
  apply isPreconnected_iUnion ⟨a,mem_iInter.mpr (fun _ => Or.inl ha)⟩
  intro z
  by_cases hz : (z:ℂ) ∈ K
  · simpa [W, connectedComponentIn_eq_empty (show (z:ℂ) ∉ Kᶜ from fun h => h hz)] using hc.isPreconnected
  let U := connectedComponentIn Kᶜ (z:ℂ)
  have hU : IsConnected U := isConnected_connectedComponentIn_iff.mpr hz
  have hUne : U ≠ univ := by
    intro h
    have haU : a ∈ U := h ▸ mem_univ a
    exact connectedComponentIn_subset Kᶜ _ haU ha
  obtain ⟨b,hb⟩ := nonempty_frontier_iff.mpr ⟨hU.nonempty,hUne⟩
  exact hc.isPreconnected.union b (frontier_complementary_component_subset K hK _ hb)
    (frontier_subset_closure hb) hU.closure.isPreconnected

/-- The complement of the filling is precisely the unique unbounded
complementary component. -/
theorem continuumFill_compl_eq_component (K : Set ℂ) (hK : IsCompact K)
    (a : ℂ) (ha : a ∉ continuumFill K) :
    (continuumFill K)ᶜ = connectedComponentIn Kᶜ a := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  let r := max R 0
  let E : Set ℂ := {z | r < ‖z‖}
  have hEc : IsConnected E := complex_norm_gt_isConnected r (le_max_right _ _)
  have hE : E ⊆ Kᶜ := by
    intro z hz hk
    exact (not_lt_of_ge ((hR z hk).trans (le_max_left _ _))) hz
  have hmeet (z : ℂ) (hz : z ∉ continuumFill K) :
      ∃ w ∈ connectedComponentIn Kᶜ z, w ∈ E := by
    by_contra! hw
    apply hz ∘ Or.inr
    exact isBounded_iff_forall_norm_le.mpr ⟨r,fun w hw' => le_of_not_gt (hw w hw')⟩
  ext z
  constructor
  · intro hz
    obtain ⟨u,hu,huE⟩ := hmeet a ha
    obtain ⟨v,hv,hvE⟩ := hmeet z hz
    have hvu := hEc.isPreconnected.subset_connectedComponentIn huE hE hvE
    have he := (connectedComponentIn_eq hv).trans
      ((connectedComponentIn_eq hvu).symm.trans (connectedComponentIn_eq hu).symm)
    exact he ▸ mem_connectedComponentIn (show z ∉ K from fun h => hz (Or.inl h))
  · intro hz
    have hzK : z ∉ K := connectedComponentIn_subset Kᶜ a hz
    intro hf
    apply ha ∘ Or.inr
    change IsBounded (connectedComponentIn Kᶜ a)
    rw [connectedComponentIn_eq hz]
    exact hf.resolve_left hzK

theorem continuumFill_compl_isConnected (K : Set ℂ) (hK : IsCompact K) :
    IsConnected (continuumFill K)ᶜ := by
  obtain ⟨R,hR⟩ := (isBounded_continuumFill K hK).exists_norm_le
  let a : ℂ := (max R 0 + 1 : ℝ)
  have ha : a ∉ continuumFill K := by
    intro h
    have h' := hR a h
    have h0 : 0 ≤ max R 0 + 1 := by positivity
    have he : ‖a‖ = max R 0 + 1 := by
      change ‖((max R 0 + 1 : ℝ):ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    rw [he] at h'
    linarith [le_max_left R 0]
  rw [continuumFill_compl_eq_component K hK a ha]
  exact isConnected_connectedComponentIn_iff.mpr (show a ∉ K from fun h => ha (Or.inl h))

end SpringerLean
