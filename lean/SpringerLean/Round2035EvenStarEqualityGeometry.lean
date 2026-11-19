import SpringerLean.Round2034EvenQuotientCoefficientIdentity

namespace SpringerLean

/-- Equality in the actual quotient second moment forces the original
omitted set to be the full `k`th-power preimage of a rotated slit. -/
theorem evenPowerQuotient_secondMoment_eq_two_omitted_preimage_slit
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (hEq : actualBoundaryRadialMoment
      (evenExteriorPowerQuotient F k) 2 = 2) :
    ∃ a : ℂ, ‖a‖ = 1 ∧
      K = {z : ℂ | z^k ∈ (slitMap a '' exteriorDisk)ᶜ} := by
  let G := evenExteriorPowerQuotient F k
  have hG := evenExteriorPowerQuotient_actual_centered
    F K k hk hF hK hImage
  obtain ⟨a, ha, hGslit⟩ :=
    (actualBoundaryRadialMoment_two_eq_iff_slit G hG).mp hEq
  have hGeom := evenExteriorPowerQuotient_actual_geometry
    F K k hk hF hK hImage
  have hImageSlit : G '' exteriorDisk = slitMap a '' exteriorDisk :=
    Set.image_congr hGslit
  have hPowerImage : (fun w : ℂ => w^k) '' K =
      (slitMap a '' exteriorDisk)ᶜ := by
    have h := hGeom.2.1
    rw [hImageSlit] at h
    exact compl_injective (by simpa only [compl_compl] using h.symm)
  have hRot := evenGeneratorInvariant_to_evenRotationInvariant K k hk hK
  refine ⟨a, ha, ?_⟩
  ext z
  change z ∈ K ↔ z^k ∈ (slitMap a '' exteriorDisk)ᶜ
  rw [← hPowerImage]
  exact (evenPower_mem_powerImage_iff K k hk hRot z).symm

/-- Saturation of the original positive Laurent coefficient already
forces the omitted set to be the preimage of a rotated slit. -/
theorem evenPowerQuotient_forwardCoeff_full_omitted_preimage_slit
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (hFull : (k:ℝ)^2 * ‖exteriorForwardCoeff F (2*k-1)‖^2 = 1) :
    ∃ a : ℂ, ‖a‖ = 1 ∧
      K = {z : ℂ | z^k ∈ (slitMap a '' exteriorDisk)ᶜ} := by
  let G := evenExteriorPowerQuotient F k
  have hG := evenExteriorPowerQuotient_actual_centered
    F K k hk hF hK hImage
  have hcoeff := evenExteriorPowerQuotient_firstCoeff_eq_k_mul_forwardCoeff
    F K k hk hF hK hImage
  have hkn : 0 ≤ (k:ℝ)*‖exteriorForwardCoeff F (2*k-1)‖ := by positivity
  have hkn1 : (k:ℝ)*‖exteriorForwardCoeff F (2*k-1)‖ = 1 := by
    nlinarith [sq_nonneg ((k:ℝ)*‖exteriorForwardCoeff F (2*k-1)‖)]
  have hbG : ‖exteriorForwardCoeff G 1‖ = 1 := by
    rw [hcoeff, norm_mul, Complex.norm_natCast]
    exact hkn1
  have hslit : ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn G (slitMap a) exteriorDisk := by
    apply (exteriorInverseCoeff_one_norm_eq_one_iff_slit G hG).mp
    rwa [exteriorInverseCoeff_one_eq_forwardCoeff_one G hG]
  have hR2 : actualBoundaryRadialMoment G 2=2 :=
    (actualBoundaryRadialMoment_two_eq_iff_slit G hG).mpr hslit
  exact evenPowerQuotient_secondMoment_eq_two_omitted_preimage_slit
    F K k hk hF hK hImage hR2

end SpringerLean
