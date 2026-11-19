import SpringerLean.Round1935OddStarActualMap
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace SpringerLean

/-- The exterior image of the star perturbation is exactly the full
inverse image of the seed's exterior image under the m-th power map. -/
theorem oddStarPerturbation_image_power_iff
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) (w : ℂ) :
    w ∈ oddStarPerturbation m t '' exteriorDisk ↔
      w ^ m ∈ oddStarSeed t '' exteriorDisk := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ^ m, by
      change 1 < ‖z ^ m‖
      rw [norm_pow]
      exact one_lt_pow₀ hz (by omega : m ≠ 0),
      (oddStarPerturbation_pow_eq_seed m (by omega) t ht z hz).symm⟩
  · rintro ⟨v, hv, hvw⟩
    obtain ⟨z, hzpow⟩ := IsAlgClosed.exists_pow_nat_eq v (by omega : 0 < m)
    have hz : z ∈ exteriorDisk := by
      change 1 < ‖z‖
      apply (one_lt_pow_iff_of_nonneg (norm_nonneg z)
        (by omega : m ≠ 0)).mp
      have hvnorm : 1 < ‖v‖ := hv
      calc
        1 < ‖v‖ := hvnorm
        _ = ‖z‖ ^ m := by rw [← hzpow, norm_pow]
    let a := oddStarPerturbation m t z
    have ha0 : a ≠ 0 := by
      have hz0 : z ≠ 0 := by
        intro h
        subst z
        have : 1 < ‖(0 : ℂ)‖ := hz
        norm_num at this
      have hu := oddStarPerturbation_reciprocal_mem_unitDisk m (by omega) z hz
      exact mul_ne_zero hz0
        (oddStarSeedRootReciprocal_ne_zero m (by omega) t ht
          (z ^ m)⁻¹ hu)
    have hpow : a ^ m = w ^ m := by
      dsimp [a]
      rw [oddStarPerturbation_pow_eq_seed m (by omega) t ht z hz,
        hzpow]
      exact hvw
    let η : ℂ := w / a
    have hηpow : η ^ m = 1 := by
      dsimp [η]
      rw [div_pow, ← hpow, div_self (pow_ne_zero _ ha0)]
    have hηnorm : ‖η‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hηpow (by omega : m ≠ 0)
    have hηz : η * z ∈ exteriorDisk := by
      change 1 < ‖η * z‖
      rw [norm_mul, hηnorm, one_mul]
      exact hz
    refine ⟨η * z, hηz, ?_⟩
    rw [oddStarPerturbation_rotation m t η z hηpow]
    change η * a = w
    dsimp [η]
    simpa only [mul_comm] using (div_mul_cancel₀ w ha0)

noncomputable def oddStarSeedOmitted (t : ℝ) : Set ℂ :=
  (oddStarSeed t '' exteriorDisk)ᶜ

noncomputable def oddStarPerturbationOmitted (m : ℕ) (t : ℝ) : Set ℂ :=
  (oddStarPerturbation m t '' exteriorDisk)ᶜ

/-- The actual omitted set is the full power preimage of the seed's
omitted set, including every branch and all boundary points. -/
theorem oddStarPerturbation_omitted_eq_power_preimage
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    oddStarPerturbationOmitted m t =
      {w : ℂ | w ^ m ∈ oddStarSeedOmitted t} := by
  ext w
  simp only [oddStarPerturbationOmitted, oddStarSeedOmitted,
    Set.mem_compl_iff, Set.mem_setOf_eq]
  exact not_congr (oddStarPerturbation_image_power_iff m hm t ht w)

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_image_power_iff
#print axioms SpringerLean.oddStarPerturbation_omitted_eq_power_preimage
