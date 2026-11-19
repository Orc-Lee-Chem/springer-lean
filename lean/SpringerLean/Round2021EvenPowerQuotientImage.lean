import SpringerLean.Round2020EvenPowerQuotientOdd

namespace SpringerLean

private theorem evenExteriorPrincipalRoot_mem
    (k : ℕ) (hk : 0 < k) (v : ℂ) (hv : v ∈ exteriorDisk) :
    v ^ ((k:ℂ)⁻¹) ∈ exteriorDisk := by
  let z : ℂ := v ^ ((k:ℂ)⁻¹)
  have hzpow : z ^ k = v := by
    simpa only [z] using Complex.cpow_nat_inv_pow v (by omega : k ≠ 0)
  have hvgt : 1 < ‖v‖ := hv
  have hnormpow : ‖z‖ ^ k = ‖v‖ := by rw [← norm_pow, hzpow]
  have hpowgt : 1 < ‖z‖ ^ k := by rw [hnormpow]; exact hvgt
  exact (one_lt_pow_iff_of_nonneg (norm_nonneg z)
    (by omega : k ≠ 0)).mp hpowgt

theorem evenExteriorPowerQuotient_injOn
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hF : Set.InjOn F exteriorDisk)
    (hcov : EvenExteriorCovariant F k) :
    Set.InjOn (evenExteriorPowerQuotient F k) exteriorDisk := by
  intro v hv w hw heq
  let z : ℂ := v ^ ((k:ℂ)⁻¹)
  let u : ℂ := w ^ ((k:ℂ)⁻¹)
  have hz : z ∈ exteriorDisk := evenExteriorPrincipalRoot_mem k hk v hv
  have hu : u ∈ exteriorDisk := evenExteriorPrincipalRoot_mem k hk w hw
  have hzpow : z ^ k = v := by
    simpa only [z] using Complex.cpow_nat_inv_pow v (by omega : k ≠ 0)
  have hupow : u ^ k = w := by
    simpa only [u] using Complex.cpow_nat_inv_pow w (by omega : k ≠ 0)
  have hFpow : (F z) ^ k = (F u) ^ k := heq
  by_cases hFu : F u = 0
  · have hFz : F z = 0 := by
      apply eq_zero_of_pow_eq_zero
      rw [hFpow, hFu]
      exact zero_pow (by omega : k ≠ 0)
    have hzu : z = u := hF hz hu (hFz.trans hFu.symm)
    calc
      v = z ^ k := hzpow.symm
      _ = u ^ k := by rw [hzu]
      _ = w := hupow
  · let η : ℂ := F z / F u
    have hηk : η ^ k = 1 := by
      dsimp [η]
      rw [div_pow, hFpow, div_self (pow_ne_zero k hFu)]
    have hη2k : η ^ (2*k) = 1 := by
      rw [mul_comm 2 k, pow_mul, hηk, one_pow]
    have hηnorm : ‖η‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hηk (by omega)
    have hηu : η*u ∈ exteriorDisk := by
      change 1 < ‖η*u‖
      rw [norm_mul, hηnorm, one_mul]
      exact hu
    have hFzu : F z = F (η*u) := by
      rw [hcov η u hη2k hu]
      dsimp [η]
      field_simp
    have hzu : z = η*u := hF hz hηu hFzu
    calc
      v = z ^ k := hzpow.symm
      _ = (η*u) ^ k := by rw [hzu]
      _ = η ^ k * u ^ k := mul_pow η u k
      _ = w := by rw [hηk, one_mul, hupow]

/-- The quotient's exterior image is exactly the power image of F's
exterior image. This is a set-theoretic statement; analyticity and
normalization of the quotient are separate. -/
theorem evenExteriorPowerQuotient_image_eq_powerImage
    (F : ℂ → ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k) :
    evenExteriorPowerQuotient F k '' exteriorDisk =
      (fun w : ℂ => w ^ k) '' (F '' exteriorDisk) := by
  ext v
  constructor
  · rintro ⟨x,hx,rfl⟩
    let z : ℂ := x ^ ((k:ℂ)⁻¹)
    have hz : z ∈ exteriorDisk := evenExteriorPrincipalRoot_mem k hk x hx
    exact ⟨F z, ⟨z,hz,rfl⟩, rfl⟩
  · rintro ⟨w, ⟨z,hz,rfl⟩, rfl⟩
    have hzk : z ^ k ∈ exteriorDisk := by
      change 1 < ‖z ^ k‖
      rw [norm_pow]
      exact one_lt_pow₀ hz (by omega : k ≠ 0)
    refine ⟨z ^ k, hzk, ?_⟩
    exact evenExteriorPowerQuotient_comp_pow F k hk hcov z hz

end SpringerLean

#print axioms SpringerLean.evenExteriorPowerQuotient_injOn
#print axioms SpringerLean.evenExteriorPowerQuotient_image_eq_powerImage
