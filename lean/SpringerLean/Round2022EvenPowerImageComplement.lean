import SpringerLean.Round2021EvenPowerQuotientImage

namespace SpringerLean

/-- Invariance of the continuum under all 2k-th root rotations. -/
def EvenRotationInvariant (K : Set ℂ) (k : ℕ) : Prop :=
  ∀ (η z : ℂ), η ^ (2*k) = 1 → z ∈ K → η*z ∈ K

theorem evenPower_mem_powerImage_iff
    (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hK : EvenRotationInvariant K k) (z : ℂ) :
    z ^ k ∈ (fun w : ℂ => w ^ k) '' K ↔ z ∈ K := by
  constructor
  · rintro ⟨w, hw, hpow⟩
    change w ^ k = z ^ k at hpow
    by_cases hz : z = 0
    · subst z
      have hw0 : w = 0 := by
        apply eq_zero_of_pow_eq_zero
        rw [hpow]
        exact zero_pow (by omega : k ≠ 0)
      simpa [hw0] using hw
    · let η : ℂ := w / z
      have hηk : η ^ k = 1 := by
        dsimp [η]
        rw [div_pow, hpow, div_self (pow_ne_zero k hz)]
      have hη2k : η ^ (2*k) = 1 := by
        rw [mul_comm 2 k, pow_mul, hηk, one_pow]
      have hηw : η*z = w := by
        dsimp [η]
        field_simp
      have hηinvk : (η⁻¹)^k = 1 := by rw [inv_pow, hηk, inv_one]
      have hηinv2k : (η⁻¹)^(2*k) = 1 := by
        rw [mul_comm 2 k, pow_mul, hηinvk, one_pow]
      have hη0 : η ≠ 0 := by
        intro heq
        rw [heq, zero_pow (by omega : k ≠ 0)] at hηk
        norm_num at hηk
      have hηw' : η⁻¹*w = z := by
        rw [← hηw, ← mul_assoc, inv_mul_cancel₀ hη0, one_mul]
      rw [← hηw']
      exact hK η⁻¹ w hηinv2k hw
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem evenPower_image_compl_eq
    (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hK : EvenRotationInvariant K k) :
    (fun w : ℂ => w ^ k) '' Kᶜ =
      ((fun w : ℂ => w ^ k) '' K)ᶜ := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (evenPower_mem_powerImage_iff K k hk hK z).not.mpr hz
  · intro hv
    let z : ℂ := v ^ ((k:ℂ)⁻¹)
    have hzpow : z ^ k = v := by
      simpa only [z] using Complex.cpow_nat_inv_pow v (by omega : k ≠ 0)
    have hz : z ∉ K := by
      intro hzk
      apply hv
      rw [← hzpow]
      exact (evenPower_mem_powerImage_iff K k hk hK z).mpr hzk
    exact ⟨z, hz, hzpow⟩

theorem evenExteriorPowerQuotient_image_compl
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k)
    (hK : EvenRotationInvariant K k)
    (hF : F '' exteriorDisk = Kᶜ) :
    evenExteriorPowerQuotient F k '' exteriorDisk =
      ((fun w : ℂ => w ^ k) '' K)ᶜ := by
  rw [evenExteriorPowerQuotient_image_eq_powerImage F k hk hcov, hF]
  exact evenPower_image_compl_eq K k hk hK

end SpringerLean

#print axioms SpringerLean.evenPower_mem_powerImage_iff
#print axioms SpringerLean.evenPower_image_compl_eq
#print axioms SpringerLean.evenExteriorPowerQuotient_image_compl
