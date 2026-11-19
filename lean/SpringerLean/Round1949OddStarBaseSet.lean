import SpringerLean.Round1948OddStarZeroSeedSegment

namespace SpringerLean

/-- Every point of [0,4] is attained by the boundary trace of the
unperturbed Joukowski seed. -/
theorem oddStarBaseSegment_subset_zero_boundary :
    oddStarBaseSegment ⊆ oddStarSeed 0 '' oddStarSeedUnitCircle := by
  intro w hw
  rcases hw with ⟨him, hlo, hhi⟩
  let x : ℝ := (w.re - 2) / 2
  have hxlo : -1 ≤ x := by dsimp [x]; linarith
  have hxhi : x ≤ 1 := by dsimp [x]; linarith
  have hxnonneg : 0 ≤ 1 - x ^ 2 := by nlinarith
  let y : ℝ := Real.sqrt (1 - x ^ 2)
  have hy2 : y ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hxnonneg
  let z : ℂ := ⟨x, y⟩
  have hznorm2 : ‖z‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, z]
    nlinarith [hy2]
  have hznorm : ‖z‖ = 1 := by
    nlinarith [norm_nonneg z]
  have hz : z ∈ oddStarSeedUnitCircle := by
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hznorm
  refine ⟨z, hz, ?_⟩
  rw [oddStarSeed_zero_boundary_formula hz]
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    dsimp [z, x]
    ring
  · simpa [Complex.ofReal_im] using him.symm

/-- The omitted set of the unperturbed seed is the actual real segment
from zero to four, with no extra interior or isolated components. -/
theorem oddStarSeed_zero_omitted_eq_segment :
    oddStarSeedOmitted 0 = oddStarBaseSegment := by
  rw [oddStarSeed_omitted_eq_boundary_image 0 (by norm_num)]
  exact Set.Subset.antisymm
    oddStarSeed_zero_boundary_subset_segment
    oddStarBaseSegment_subset_zero_boundary

/-- A regular m-armed star of capacity-one scale, expressed as the full
power preimage of the real segment [0,4]. -/
def regularStarPowerSet (m : ℕ) : Set ℂ :=
  {w : ℂ | w ^ m ∈ oddStarBaseSegment}

/-- At t=0, the actual exterior perturbation omits precisely the
regular m-armed star, as an equality of plane sets. -/
theorem oddStarPerturbation_zero_omitted_eq_regularStar
    (m : ℕ) (hm : 2 ≤ m) :
    oddStarPerturbationOmitted m 0 = regularStarPowerSet m := by
  rw [oddStarPerturbation_omitted_eq_power_preimage m hm 0 (by norm_num),
    oddStarSeed_zero_omitted_eq_segment]
  rfl

end SpringerLean

#print axioms SpringerLean.oddStarSeed_zero_omitted_eq_segment
#print axioms SpringerLean.oddStarPerturbation_zero_omitted_eq_regularStar
