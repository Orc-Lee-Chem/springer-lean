import SpringerLean.Round2029ExteriorMapUniqueness

namespace SpringerLean

theorem evenExteriorPowerQuotient_actual_geometry
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    Set.InjOn (evenExteriorPowerQuotient F k) exteriorDisk ∧
      evenExteriorPowerQuotient F k '' exteriorDisk =
        ((fun w : ℂ => w ^ k) '' K)ᶜ ∧
      (∀ v ∈ exteriorDisk,
        evenExteriorPowerQuotient F k (-v) =
          -evenExteriorPowerQuotient F k v) := by
  have hcov := evenExteriorCovariant_actual F K k hk hF hK hImage
  exact ⟨evenExteriorPowerQuotient_injOn F k hk hF.2.1 hcov,
    evenExteriorPowerQuotient_image_compl_of_generator
      F K k hk hcov hK hImage,
    evenExteriorPowerQuotient_odd F k hk hcov⟩

theorem evenExteriorPowerQuotient_actual_secondMoment_of_centered
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (hG : CenteredExteriorUnivalent (evenExteriorPowerQuotient F k)) :
    actualBoundaryRadialMoment (evenExteriorPowerQuotient F k) 2 ≤
      2 - (2/3:ℝ) *
        (1 - ‖exteriorForwardCoeff (evenExteriorPowerQuotient F k) 1‖^2) := by
  have hcov := evenExteriorCovariant_actual F K k hk hF hK hImage
  exact evenExteriorPowerQuotient_secondMoment_margin F k hk hcov hG

end SpringerLean

#print axioms SpringerLean.evenExteriorPowerQuotient_actual_geometry
#print axioms SpringerLean.evenExteriorPowerQuotient_actual_secondMoment_of_centered
