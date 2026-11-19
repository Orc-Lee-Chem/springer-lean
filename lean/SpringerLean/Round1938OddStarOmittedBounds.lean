import SpringerLean.Round1937OddStarOmittedTips
import SpringerLean.Round480OmittedRadius
import SpringerLean.Round12Compact

namespace SpringerLean

/-- The actual odd-star omitted set is compact. -/
theorem oddStarPerturbation_omitted_isCompact
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    IsCompact (oddStarPerturbationOmitted m t) := by
  exact exteriorOmitted_isCompact
    (oddStarPerturbation m t)
    (oddStarPerturbation_centeredExteriorUnivalent m hm t ht)

/-- All points of the actual odd-star omitted set lie in the closed
radius-two disk, in the capacity-one exterior normalization. -/
theorem oddStarPerturbation_omitted_norm_le_two
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    {w : ℂ} (hw : w ∈ oddStarPerturbationOmitted m t) :
    ‖w‖ ≤ 2 := by
  exact exteriorOmitted_norm_le_two
    (oddStarPerturbation m t)
    (oddStarPerturbation_centeredExteriorUnivalent m hm t ht) hw

/-- The omitted set inherits exact m-fold rotational symmetry. -/
theorem oddStarPerturbation_omitted_rotation_iff
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (η w : ℂ) (hη : η ^ m = 1) :
    η * w ∈ oddStarPerturbationOmitted m t ↔
      w ∈ oddStarPerturbationOmitted m t := by
  rw [oddStarPerturbation_omitted_eq_power_preimage m hm t ht]
  simp only [Set.mem_setOf_eq, mul_pow, hη, one_mul]

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_omitted_norm_le_two
#print axioms SpringerLean.oddStarPerturbation_omitted_rotation_iff
#print axioms SpringerLean.oddStarPerturbation_omitted_isCompact
