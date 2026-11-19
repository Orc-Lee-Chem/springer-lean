import SpringerLean.Round1947FactorLinearFamilies

namespace SpringerLean

/-- The real segment from zero to four, embedded in the complex plane. -/
def oddStarBaseSegment : Set ℂ :=
  {w : ℂ | w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ 4}

/-- On the unit circle the unperturbed seed has its familiar
real-valued Joukowski boundary trace. -/
theorem oddStarSeed_zero_boundary_formula
    {z : ℂ} (hz : z ∈ oddStarSeedUnitCircle) :
    oddStarSeed 0 z = ((2 + 2 * z.re : ℝ) : ℂ) := by
  have hnorm : ‖z‖ = 1 := by
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    norm_num at hnorm
  rw [oddStarSeed_zero_expansion z hz0, Complex.inv_eq_conj hnorm]
  apply Complex.ext
  · simp [Complex.add_re, Complex.conj_re]
    ring
  · simp [Complex.add_im, Complex.conj_im]

/-- Every seed boundary value at t=0 lies on [0,4]. -/
theorem oddStarSeed_zero_boundary_subset_segment :
    oddStarSeed 0 '' oddStarSeedUnitCircle ⊆ oddStarBaseSegment := by
  rintro w ⟨z, hz, rfl⟩
  rw [oddStarSeed_zero_boundary_formula hz]
  have hnorm : ‖z‖ = 1 := by
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hz
  have hre : |z.re| ≤ 1 := by
    simpa [hnorm] using Complex.abs_re_le_norm z
  rcases abs_le.mp hre with ⟨hl, hr⟩
  simp only [oddStarBaseSegment, Set.mem_setOf_eq, Complex.ofReal_im,
    Complex.ofReal_re, true_and]
  constructor <;> linarith

end SpringerLean

#print axioms SpringerLean.oddStarSeed_zero_boundary_formula
#print axioms SpringerLean.oddStarSeed_zero_boundary_subset_segment
