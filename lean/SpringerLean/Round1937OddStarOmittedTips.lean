import SpringerLean.Round1936OddStarOmittedPower

namespace SpringerLean

/-- The zero tip is omitted by the seed's open exterior image. -/
theorem oddStarSeed_zero_mem_omitted
    (t : ℝ) (ht : |t| < 1) :
    (0 : ℂ) ∈ oddStarSeedOmitted t := by
  intro h
  obtain ⟨z, hz, heq⟩ := h
  have hden := oddStarSeed_denominator_ne_zero t ht z hz
  have htip := (oddStarSeed_tip_norms t ht).1
  have hnum : z - (t : ℂ) * Complex.I +
      (Real.sqrt (1 - t ^ 2) : ℂ) ≠ 0 := by
    intro hzero
    have hz' : z = (t : ℂ) * Complex.I -
        (Real.sqrt (1 - t ^ 2) : ℂ) := by
      linear_combination hzero
    have hznorm : 1 < ‖z‖ := hz
    rw [hz', htip] at hznorm
    linarith
  have hnonzero : oddStarSeed t z ≠ 0 := by
    unfold oddStarSeed
    exact div_ne_zero (pow_ne_zero _ hnum) hden
  exact hnonzero heq

/-- The outer tip at 4 sqrt(1-t²) is also omitted by the open image. -/
theorem oddStarSeed_four_s_mem_omitted
    (t : ℝ) (ht : |t| < 1) :
    ((4 * Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) ∈
      oddStarSeedOmitted t := by
  intro h
  obtain ⟨z, hz, heq⟩ := h
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  have hden := oddStarSeed_denominator_ne_zero t ht z hz
  have htip := (oddStarSeed_tip_norms t ht).2
  have hmain :
      (z - (t : ℂ) * Complex.I + (s : ℂ)) ^ 2 =
        (4 * s : ℝ) * (z - (t : ℂ) * Complex.I) := by
    unfold oddStarSeed at heq
    change (z - (t : ℂ) * Complex.I + (s : ℂ)) ^ 2 /
        (z - (t : ℂ) * Complex.I) = (4 * s : ℝ) at heq
    exact (div_eq_iff hden).mp heq
  have hsq : (z - (t : ℂ) * Complex.I - (s : ℂ)) ^ 2 = 0 := by
    calc
      _ = (z - (t : ℂ) * Complex.I + (s : ℂ)) ^ 2 -
          (4 * s : ℝ) * (z - (t : ℂ) * Complex.I) := by
            push_cast
            ring
      _ = 0 := sub_eq_zero.mpr hmain
  have hz' : z = (t : ℂ) * Complex.I + (s : ℂ) := by
    have hlinear : z - (t : ℂ) * Complex.I - (s : ℂ) = 0 :=
      sq_eq_zero_iff.mp hsq
    linear_combination hlinear
  have hznorm : 1 < ‖z‖ := hz
  rw [hz', htip] at hznorm
  linarith

/-- The star omitted set contains the origin and every m-th root of
the outer seed tip. -/
theorem oddStarPerturbation_omitted_tips
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    (0 : ℂ) ∈ oddStarPerturbationOmitted m t ∧
      ∀ w : ℂ,
        w ^ m = ((4 * Real.sqrt (1 - t ^ 2) : ℝ) : ℂ) →
          w ∈ oddStarPerturbationOmitted m t := by
  rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht]
  constructor
  · simpa [zero_pow (by omega : m ≠ 0)] using
      oddStarSeed_zero_mem_omitted t ht
  · intro w hw
    change w ^ m ∈ oddStarSeedOmitted t
    rw [hw]
    exact oddStarSeed_four_s_mem_omitted t ht

end SpringerLean

#print axioms SpringerLean.oddStarSeed_zero_mem_omitted
#print axioms SpringerLean.oddStarSeed_four_s_mem_omitted
#print axioms SpringerLean.oddStarPerturbation_omitted_tips
