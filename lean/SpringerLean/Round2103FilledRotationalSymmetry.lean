import SpringerLean.Round2094FilledContinuumTopology
import SpringerLean.Round2023EvenGeneratorSymmetry

open Set Bornology

namespace SpringerLean

/-- The rotation of an invariant compact set takes a complementary
component onto the corresponding complementary component. -/
theorem image_complementary_component_rotate
    (K : Set ℂ) (η : ℂ) (hη : η ≠ 0)
    (hK : ∀ z : ℂ, η*z ∈ K ↔ z ∈ K) (a : ℂ) (ha : a ∉ K) :
    (fun z : ℂ => η*z) '' connectedComponentIn Kᶜ a =
      connectedComponentIn Kᶜ (η*a) := by
  let f (z : ℂ) := η*z
  let g (z : ℂ) := η⁻¹*z
  have hfg (z : ℂ) : f (g z) = z := by simp [f,g, ← mul_assoc,hη]
  have hgf (z : ℂ) : g (f z) = z := by simp [f,g, ← mul_assoc,hη]
  have hf : Continuous f := by unfold f; fun_prop
  have hg : Continuous g := by unfold g; fun_prop
  have hfK : f '' Kᶜ ⊆ Kᶜ := by
    rintro w ⟨z,hz,rfl⟩
    exact fun hw => hz ((hK z).mp hw)
  have hgK : g '' Kᶜ ⊆ Kᶜ := by
    rintro w ⟨z,hz,rfl⟩
    intro hw
    have he : f (g z) ∈ K := (hK (g z)).mpr hw
    exact hz (by simpa only [hfg] using he)
  have haf : f a ∈ Kᶜ := hfK (mem_image_of_mem f ha)
  apply Subset.antisymm
  · exact (hf.continuousOn.image_connectedComponentIn_subset ha).trans (connectedComponentIn_mono _ hfK)
  · intro z hz
    have hgz := (hg.continuousOn.image_connectedComponentIn_subset haf).trans (connectedComponentIn_mono _ hgK)
      (mem_image_of_mem g hz)
    rw [hgf] at hgz
    exact ⟨g z,hgz,hfg z⟩

/-- Filling preserves every unit rotational symmetry of the original set. -/
theorem continuumFill_rotate_mem
    (K : Set ℂ) (η : ℂ) (hη : ‖η‖ = 1)
    (hK : ∀ z : ℂ, η*z ∈ K ↔ z ∈ K) (a : ℂ) (ha : a ∈ continuumFill K) :
    η*a ∈ continuumFill K := by
  by_cases haK : a ∈ K
  · exact Or.inl ((hK a).mpr haK)
  have hn : η ≠ 0 := by intro h; simp [h] at hη
  have hb : IsBounded (connectedComponentIn Kᶜ a) := ha.resolve_left haK
  obtain ⟨C,hC⟩ := hb.exists_norm_le
  apply Or.inr
  change IsBounded (connectedComponentIn Kᶜ (η*a))
  rw [←image_complementary_component_rotate K η hn hK a haK]
  refine isBounded_iff_forall_norm_le.mpr ⟨C,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  simpa only [norm_mul,hη,one_mul] using hC z hz

theorem continuumFill_evenGeneratorInvariant (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hK : EvenGeneratorInvariant K k) : EvenGeneratorInvariant (continuumFill K) k := by
  let η := Complex.exp (2*Real.pi*Complex.I/((2*k : ℕ):ℂ))
  have hη : IsPrimitiveRoot η (2*k) := Complex.isPrimitiveRoot_exp _ (by omega)
  have hn := Complex.norm_eq_one_of_pow_eq_one hη.pow_eq_one (by omega : 2*k ≠ 0)
  have hη0 : η ≠ 0 := by intro he; simp [he] at hn
  have h := evenGeneratorInvariant_to_evenRotationInvariant K k hk hK
  apply continuumFill_rotate_mem K η hn
  intro z
  refine ⟨fun hz => ?_,h η z hη.pow_eq_one⟩
  have he : (η⁻¹)^(2*k) = 1 := by rw [inv_pow,hη.pow_eq_one,inv_one]
  have h' := h η⁻¹ (η*z) he hz
  rwa [←mul_assoc,inv_mul_cancel₀ hη0,one_mul] at h'

theorem continuumFill_eq_self_if_interior_empty (K : Set ℂ) (hK : IsClosed K)
    (h : interior (continuumFill K) = ∅) : continuumFill K = K := by
  apply Subset.antisymm _ (subset_continuumFill K)
  intro z hz
  by_contra hn
  have he := continuumFill_diff_subset_interior K hK ⟨hz,hn⟩
  rw [h] at he
  exact he.elim

end SpringerLean
