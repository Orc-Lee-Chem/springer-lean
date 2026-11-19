import SpringerLean.Round1931OddStarPowerBridge

namespace SpringerLean

theorem oddStarSeedReciprocal_ne_zero
    (t : ℝ) (ht : |t| < 1) (u : ℂ) (hu : ‖u‖ < 1) :
    oddStarSeedReciprocal t u ≠ 0 := by
  unfold oddStarSeedReciprocal
  apply div_ne_zero
  · exact pow_ne_zero _
      (oddStarSeed_reciprocal_numerator_ne_zero t ht u hu)
  · exact oddStarSeed_reciprocal_denominator_ne_zero t ht u hu

theorem oddStarSeedRootReciprocal_ne_zero
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| < 1)
    (u : ℂ) (hu : ‖u‖ < 1) :
    oddStarSeedRootReciprocal m t u ≠ 0 := by
  intro hzero
  have hpow := oddStarSeedRootReciprocal_pow m hm t u
  rw [hzero, zero_pow (Nat.ne_of_gt hm)] at hpow
  exact (oddStarSeedReciprocal_ne_zero t ht u hu) hpow.symm

/-- The explicit odd-star perturbation is univalent on the open
exterior disk for every positive order. -/
theorem oddStarPerturbation_injOn_exteriorDisk
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| < 1) :
    Set.InjOn (oddStarPerturbation m t) exteriorDisk := by
  intro z hz w hw heq
  have hzn : 1 < ‖z‖ := hz
  have hwn : 1 < ‖w‖ := hw
  have hzpow : z ^ m ∈ exteriorDisk := by
    change 1 < ‖z ^ m‖
    rw [norm_pow]
    exact one_lt_pow₀ hzn (Nat.ne_of_gt hm)
  have hwpow : w ^ m ∈ exteriorDisk := by
    change 1 < ‖w ^ m‖
    rw [norm_pow]
    exact one_lt_pow₀ hwn (Nat.ne_of_gt hm)
  have hseed : oddStarSeed t (z ^ m) = oddStarSeed t (w ^ m) := by
    rw [← oddStarPerturbation_pow_eq_seed m hm t ht z hz,
      ← oddStarPerturbation_pow_eq_seed m hm t ht w hw]
    exact congrArg (fun x : ℂ => x ^ m) heq
  have hpowequal : z ^ m = w ^ m :=
    oddStarSeed_injOn_exteriorDisk t ht hzpow hwpow hseed
  let u : ℂ := (z ^ m)⁻¹
  have hu : ‖u‖ < 1 :=
    oddStarPerturbation_reciprocal_mem_unitDisk m hm z hz
  have hroot : oddStarSeedRootReciprocal m t u ≠ 0 :=
    oddStarSeedRootReciprocal_ne_zero m hm t ht u hu
  have heq' : z * oddStarSeedRootReciprocal m t u =
      w * oddStarSeedRootReciprocal m t u := by
    simpa only [oddStarPerturbation, u, hpowequal] using heq
  exact mul_right_cancel₀ hroot heq'

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_injOn_exteriorDisk
