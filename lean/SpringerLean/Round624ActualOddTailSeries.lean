import SpringerLean.Round482OmittedRootEnergy
import SpringerLean.DiskExpansion

namespace SpringerLean
set_option Elab.async false

/-- The actual exterior map's odd tail, with its actual derivative-defined
coefficients. This is not a formal-series or coefficient assumption. -/
theorem exterior_odd_tail_hasSum
    (H : ℂ → ℂ) (hc : CenteredExteriorUnivalent H)
    (hodd : ∀ z, H (-z) = -H z)
    {z : ℂ} (hz : z ∈ exteriorDisk) :
    HasSum (fun k : ℕ => exteriorForwardCoeff H (2*k+3)*(z⁻¹)^(2*k+3))
      (H z-z-exteriorForwardCoeff H 1*z⁻¹) := by
  have hz0 := exterior_ne_zero hz
  have hu : ‖z⁻¹‖ < 1 := by
    rw [norm_inv]
    simpa only [one_div,inv_one] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hz
  have hs := exteriorForwardGerm_hasSum_coeff_unitBall H hc hu
  have ht := (hasSum_nat_add_iff' 2).mpr hs
  have hzero : exteriorForwardCoeff H 0 = 0 := by
    simp [exteriorForwardCoeff,exteriorForwardGerm]
  have hfg : exteriorForwardGerm H z⁻¹ = H z-z := by
    simpa only [inv_inv] using exteriorForwardGerm_punctured H (inv_ne_zero hz0)
  have ht' : HasSum (fun j : ℕ => exteriorForwardCoeff H (j+2)*(z⁻¹)^(j+2))
      (H z-z-exteriorForwardCoeff H 1*z⁻¹) := by
    simpa [Finset.sum_range_succ,hzero,hfg] using ht
  have hi : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro a b hab
    dsimp only at hab
    omega
  have hout : ∀ m : ℕ, m ∉ Set.range (fun k : ℕ => 2*k+1) →
      exteriorForwardCoeff H (m+2)*(z⁻¹)^(m+2) = 0 := by
    intro m hm
    have he : Even m := by
      rcases Nat.even_or_odd m with he | ho
      · exact he
      · exfalso
        apply hm
        obtain ⟨k,hk⟩ := ho
        exact ⟨k,by dsimp only; omega⟩
    obtain ⟨k,hk⟩ := he
    rw [show m+2 = 2*(k+1) by omega,
      exteriorForwardCoeff_even_eq_zero_of_odd H hodd (k+1),zero_mul]
  have hs' := (hi.hasSum_iff hout).mpr ht'
  simpa [Function.comp_def,Nat.add_assoc] using hs'

end SpringerLean
