import SpringerLean.Round1930OddStarAnalyticRoot

namespace SpringerLean

noncomputable def oddStarPerturbation
    (m : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  z * oddStarSeedRootReciprocal m t (z ^ m)⁻¹

theorem oddStarPerturbation_reciprocal_mem_unitDisk
    (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ∈ exteriorDisk) :
    ‖(z ^ m)⁻¹‖ < 1 := by
  change 1 < ‖z‖ at hz
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hpow : 1 < ‖z ^ m‖ := by
    rw [norm_pow]
    exact one_lt_pow₀ hz hm0
  rw [norm_inv]
  exact inv_lt_one_of_one_lt₀ hpow

/-- The analytic root construction has exactly the required power-map
identity on the original open exterior disk. -/
theorem oddStarPerturbation_pow_eq_seed
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| < 1)
    (z : ℂ) (hz : z ∈ exteriorDisk) :
    (oddStarPerturbation m t z) ^ m = oddStarSeed t (z ^ m) := by
  have hz0 : z ≠ 0 := by
    intro heq
    subst z
    have : 1 < ‖(0 : ℂ)‖ := hz
    norm_num at this
  have hzm0 : z ^ m ≠ 0 := pow_ne_zero _ hz0
  let u : ℂ := (z ^ m)⁻¹
  have hu : u ≠ 0 := inv_ne_zero hzm0
  have hunorm : ‖u‖ < 1 := oddStarPerturbation_reciprocal_mem_unitDisk m hm z hz
  have hden := oddStarSeed_reciprocal_denominator_ne_zero t ht u hunorm
  have hrec := oddStarSeed_reciprocal_identity t u hu hden
  have hroot := oddStarSeedRootReciprocal_pow m hm t u
  have hinv : u⁻¹ = z ^ m := inv_inv _
  rw [hinv] at hrec
  calc
    (oddStarPerturbation m t z) ^ m =
        z ^ m * oddStarSeedReciprocal t u := by
      simp only [oddStarPerturbation, mul_pow]
      change z ^ m * (oddStarSeedRootReciprocal m t u) ^ m = _
      rw [hroot]
    _ = oddStarSeed t (z ^ m) := by
      rw [← hrec]
      dsimp [u]
      rw [← mul_assoc, mul_inv_cancel₀ hzm0, one_mul]

/-- The constructed star perturbation is holomorphic on the actual
open exterior disk. -/
theorem oddStarPerturbation_analyticOnNhd_exteriorDisk
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : |t| < 1) :
    AnalyticOnNhd ℂ (oddStarPerturbation m t) exteriorDisk := by
  have hpow : AnalyticOnNhd ℂ (fun z : ℂ => z ^ m) exteriorDisk := by
    fun_prop
  have hinv : AnalyticOnNhd ℂ
      (fun z : ℂ => (z ^ m)⁻¹) exteriorDisk :=
    hpow.inv (by
      intro z hz
      have hz0 : z ≠ 0 := by
        intro heq
        subst z
        have : 1 < ‖(0 : ℂ)‖ := hz
        norm_num at this
      exact pow_ne_zero _ hz0)
  have hroot := oddStarSeedRootReciprocal_analyticOnNhd_unitDisk m t ht
  have hmaps : Set.MapsTo (fun z : ℂ => (z ^ m)⁻¹)
      exteriorDisk (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have h := oddStarPerturbation_reciprocal_mem_unitDisk m hm z hz
    simpa [Metric.mem_ball, dist_zero_right] using h
  have hcomp := hroot.comp hinv hmaps
  change AnalyticOnNhd ℂ
    (fun z : ℂ => oddStarSeedRootReciprocal m t (z ^ m)⁻¹)
      exteriorDisk at hcomp
  change AnalyticOnNhd ℂ
    (fun z : ℂ => z * oddStarSeedRootReciprocal m t (z ^ m)⁻¹)
      exteriorDisk
  exact analyticOnNhd_id.mul hcomp

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_pow_eq_seed
#print axioms SpringerLean.oddStarPerturbation_analyticOnNhd_exteriorDisk
