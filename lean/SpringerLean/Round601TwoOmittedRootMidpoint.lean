import SpringerLean.Round482OmittedRootEnergy

namespace SpringerLean
set_option Elab.async false

noncomputable def exteriorRootMidpoint (H J : ℂ → ℂ) (z : ℂ) : ℂ :=
  (H z + J z) / 2

theorem exteriorRootMidpoint_forwardGerm (H J : ℂ → ℂ) :
    exteriorForwardGerm (exteriorRootMidpoint H J) =
      fun u => (exteriorForwardGerm H u + exteriorForwardGerm J u) / 2 := by
  funext u
  by_cases hu : u = 0
  · simp [hu, exteriorForwardGerm_zero]
  · rw [exteriorForwardGerm_punctured _ hu,
      exteriorForwardGerm_punctured _ hu, exteriorForwardGerm_punctured _ hu]
    dsimp only [exteriorRootMidpoint]
    ring

theorem exteriorRootMidpoint_recover_left
    (H J : ℂ → ℂ) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q)
    {z : ℂ} (hz : z ∈ exteriorDisk) :
    exteriorRootMidpoint H J z ≠ 0 ∧
      H z = exteriorRootMidpoint H J z + q / exteriorRootMidpoint H J z := by
  have he := hs z hz
  have hv : exteriorRootMidpoint H J z ≠ 0 := by
    intro hv
    have hsum : H z + J z = 0 := by
      simpa only [exteriorRootMidpoint, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
        using hv
    have hJ : J z = -H z := by linear_combination hsum
    rw [hJ] at he
    have hq0 : q = 0 := by linear_combination (-1 / 4 : ℂ) * he
    exact hq hq0
  refine ⟨hv, ?_⟩
  apply mul_right_cancel₀ hv
  rw [add_mul, div_mul_cancel₀ _ hv]
  dsimp only [exteriorRootMidpoint]
  linear_combination (1 / 4 : ℂ) * he

theorem exteriorRootMidpoint_centeredExteriorUnivalent
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) (q : ℂ) (hq : q ≠ 0)
    (hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * q) :
    CenteredExteriorUnivalent (exteriorRootMidpoint H J) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact ((hH.1 z hz).add (hJ.1 z hz)).div_const 2
  · intro z hz w hw he
    have hzH := (exteriorRootMidpoint_recover_left H J q hq hs hz).2
    have hwH := (exteriorRootMidpoint_recover_left H J q hq hs hw).2
    apply hH.2.1 hz hw
    rw [hzH, hwH, he]
  · rw [exteriorRootMidpoint_forwardGerm]
    exact (hH.2.2.add hJ.2.2).div_const

theorem exteriorRootMidpoint_forwardCoeff_one
    (H J : ℂ → ℂ) (hH : CenteredExteriorUnivalent H)
    (hJ : CenteredExteriorUnivalent J) :
    exteriorForwardCoeff (exteriorRootMidpoint H J) 1 =
      (exteriorForwardCoeff H 1 + exteriorForwardCoeff J 1) / 2 := by
  have hd := (hH.2.2.differentiableAt.hasDerivAt.add
    hJ.2.2.differentiableAt.hasDerivAt).div_const (2 : ℂ)
  simp only [exteriorForwardCoeff, iteratedDeriv_one, Nat.factorial_one,
    Nat.cast_one, div_one, exteriorRootMidpoint_forwardGerm]
  exact hd.deriv

/-- The actual midpoint map used in the two-omitted-point argument. This
constructs the univalent midpoint and its exact first coefficient; the
reciprocal energy/rearrangement estimate remains a separate step. -/
theorem exteriorOmitted_exists_root_midpoint
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (A P : ℂ)
    (hA : A ∈ exteriorOmitted F) (hP : P ∈ exteriorOmitted F) (hAP : A ≠ P) :
    ∃ H J : ℂ → ℂ,
      CenteredExteriorUnivalent H ∧ CenteredExteriorUnivalent J ∧
      (∀ z, H (-z) = -H z) ∧ (∀ z, J (-z) = -J z) ∧
      (∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - A) ∧
      (∀ z ∈ exteriorDisk, J z ^ 2 = F (z ^ 2) - P) ∧
      CenteredExteriorUnivalent (exteriorRootMidpoint H J) ∧
      exteriorForwardCoeff (exteriorRootMidpoint H J) 1 = -(A + P) / 4 ∧
      ∀ z ∈ exteriorDisk, exteriorRootMidpoint H J z ≠ 0 ∧
        H z = exteriorRootMidpoint H J z +
          ((P - A) / 4) / exteriorRootMidpoint H J z := by
  obtain ⟨H, hH, hoH, hbH, _, hsH, _⟩ :=
    exteriorOmitted_exists_odd_root_with_energy F hc hA
  obtain ⟨J, hJ, hoJ, hbJ, _, hsJ, _⟩ :=
    exteriorOmitted_exists_odd_root_with_energy F hc hP
  have hq : (P - A) / 4 ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr hAP.symm) (by norm_num)
  have hs : ∀ z ∈ exteriorDisk, H z ^ 2 - J z ^ 2 = 4 * ((P - A) / 4) := by
    intro z hz
    rw [hsH z hz, hsJ z hz]
    ring
  refine ⟨H, J, hH, hJ, hoH, hoJ, hsH, hsJ,
    exteriorRootMidpoint_centeredExteriorUnivalent H J hH hJ _ hq hs, ?_, ?_⟩
  · rw [exteriorRootMidpoint_forwardCoeff_one H J hH hJ, hbH, hbJ]
    ring
  · exact fun z hz => exteriorRootMidpoint_recover_left H J _ hq hs hz

end SpringerLean
