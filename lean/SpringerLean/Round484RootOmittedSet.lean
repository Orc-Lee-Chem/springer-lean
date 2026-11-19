import SpringerLean.Round482OmittedRootEnergy

namespace SpringerLean
set_option Elab.async false

/-- The omitted set of the odd square-root map is the actual square preimage
of the original omitted set; no Jordan-boundary assumption is involved. -/
theorem odd_squareRoot_omitted_iff
    (F H : ℂ → ℂ) (P : ℂ)
    (hodd : ∀ z, H (-z) = -H z)
    (hsquare : ∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - P) (u : ℂ) :
    u ∈ exteriorOmitted H ↔ u ^ 2 + P ∈ exteriorOmitted F := by
  have hsquaredDomain {z : ℂ} (hz : z ∈ exteriorDisk) : z ^ 2 ∈ exteriorDisk := by
    change 1 < ‖z ^ 2‖
    rw [norm_pow]
    have hz1 : 1 < ‖z‖ := hz
    nlinarith [norm_nonneg z]
  constructor
  · intro hu himage
    obtain ⟨v, hv, hvEq⟩ := himage
    obtain ⟨z, hz2⟩ := IsAlgClosed.exists_pow_nat_eq v (by norm_num : 0 < (2 : ℕ))
    have hz : z ∈ exteriorDisk := by
      have hn : ‖z‖ ^ 2 = ‖v‖ := by rw [← norm_pow, hz2]
      have hv1 : 1 < ‖v‖ := hv
      change 1 < ‖z‖
      nlinarith [norm_nonneg z]
    have hs := hsquare z hz
    rw [hz2, hvEq] at hs
    have hf : (H z - u) * (H z + u) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hf with h | h
    · exact hu ⟨z, hz, sub_eq_zero.mp h⟩
    · have hneg : -z ∈ exteriorDisk := by
        change 1 < ‖-z‖
        rw [norm_neg]
        exact hz
      exact hu ⟨-z, hneg, by rw [hodd]; linear_combination -h⟩
  · intro hu himage
    obtain ⟨z, hz, hzu⟩ := himage
    have hs := hsquare z hz
    rw [hzu] at hs
    exact hu ⟨z ^ 2, hsquaredDomain hz, by linear_combination -hs⟩

theorem exteriorOmitted_exists_root_with_omitted_set
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {P : ℂ}
    (hP : P ∈ exteriorOmitted F) :
    ∃ H : ℂ → ℂ, CenteredExteriorUnivalent H ∧
      (∀ z, H (-z) = -H z) ∧
      exteriorForwardCoeff H 1 = -P / 2 ∧
      (∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - P) ∧
      ∀ u : ℂ, u ∈ exteriorOmitted H ↔ u ^ 2 + P ∈ exteriorOmitted F := by
  obtain ⟨H, hH, ho, hb, he, hs, henergy⟩ :=
    exteriorOmitted_exists_odd_root_with_energy F hc hP
  exact ⟨H, hH, ho, hb, hs, odd_squareRoot_omitted_iff F H P ho hs⟩

end SpringerLean
