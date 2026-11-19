import SpringerLean.Round2024RotatedExteriorClass

namespace SpringerLean

theorem rotateCenteredExterior_image_eq_compl
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hK : EvenRotationInvariant K k)
    (hF : F '' exteriorDisk = Kᶜ)
    (η : ℂ) (hη : η ^ (2*k) = 1) :
    rotateCenteredExterior F η '' exteriorDisk = Kᶜ := by
  have hη0 : η ≠ 0 := by
    intro heq
    rw [heq, zero_pow (by omega : 2*k ≠ 0)] at hη
    norm_num at hη
  have hηnorm : ‖η‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hη (by omega)
  have hηinvnorm : ‖η⁻¹‖ = 1 := by rw [norm_inv, hηnorm, inv_one]
  have hηinvroot : (η⁻¹) ^ (2*k) = 1 := by
    rw [inv_pow, hη, inv_one]
  have hηmem (z : ℂ) (hz : z ∈ exteriorDisk) : η*z ∈ exteriorDisk := by
    change 1 < ‖η*z‖
    rw [norm_mul, hηnorm, one_mul]
    exact hz
  have hηinvmem (z : ℂ) (hz : z ∈ exteriorDisk) : η⁻¹*z ∈ exteriorDisk := by
    change 1 < ‖η⁻¹*z‖
    rw [norm_mul, hηinvnorm, one_mul]
    exact hz
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change η⁻¹ * F (η*z) ∉ K
    intro hmem
    have hrot := hK η (η⁻¹ * F (η*z)) hη hmem
    have hFz : F (η*z) ∈ K := by
      simpa [mul_assoc, hη0] using hrot
    have hImage : F (η*z) ∈ F '' exteriorDisk :=
      ⟨η*z, hηmem z hz, rfl⟩
    rw [hF] at hImage
    exact hImage hFz
  · intro hy
    have hηy : η*y ∉ K := by
      intro hmem
      have hrot := hK η⁻¹ (η*y) hηinvroot hmem
      have hyK : y ∈ K := by simpa [mul_assoc, hη0] using hrot
      exact hy hyK
    have hηimage : η*y ∈ F '' exteriorDisk := by rw [hF]; exact hηy
    obtain ⟨z, hz, hFz⟩ := hηimage
    let x : ℂ := η⁻¹*z
    have hx : x ∈ exteriorDisk := hηinvmem z hz
    refine ⟨x, hx, ?_⟩
    change η⁻¹ * F (η*x) = y
    have hηx : η*x = z := by dsimp [x]; field_simp
    rw [hηx, hFz]
    field_simp

/-- The exact normalized exterior-map uniqueness property required
to turn set symmetry into map covariance. This property is not yet
proved for arbitrary continua in this project. -/
def NormalizedExteriorMapUnique (F : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ G : ℂ → ℂ, CenteredExteriorUnivalent G →
    G '' exteriorDisk = Kᶜ → Set.EqOn G F exteriorDisk

theorem evenExteriorCovariant_of_map_unique
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hc : CenteredExteriorUnivalent F)
    (hK : EvenRotationInvariant K k)
    (hF : F '' exteriorDisk = Kᶜ)
    (hUnique : NormalizedExteriorMapUnique F K) :
    EvenExteriorCovariant F k := by
  intro η z hη hz
  have hηnorm : ‖η‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hη (by omega)
  have hη0 : η ≠ 0 := by
    intro heq
    simp [heq, zero_pow (by omega : 2*k ≠ 0)] at hη
  have hRotClass := rotateCenteredExterior_centeredExteriorUnivalent
    F hc η hηnorm
  have hRotImage := rotateCenteredExterior_image_eq_compl
    F K k hk hK hF η hη
  have hEq := hUnique (rotateCenteredExterior F η) hRotClass hRotImage hz
  change η⁻¹ * F (η*z) = F z at hEq
  calc
    F (η*z) = η * (η⁻¹ * F (η*z)) := by field_simp
    _ = η * F z := by rw [hEq]

end SpringerLean

#print axioms SpringerLean.rotateCenteredExterior_image_eq_compl
#print axioms SpringerLean.evenExteriorCovariant_of_map_unique
