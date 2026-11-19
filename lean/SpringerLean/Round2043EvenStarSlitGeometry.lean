import SpringerLean.Round2042EvenActualBoundaryPushforward
import SpringerLean.Round1949OddStarBaseSet

namespace SpringerLean

/-- The omitted set of the unrotated slit map is the segment [-2,2]. -/
theorem slitMap_one_omitted_eq_segment :
    (slitMap 1 '' exteriorDisk)ᶜ =
      {w : ℂ | w.im = 0 ∧ -2 ≤ w.re ∧ w.re ≤ 2} := by
  ext w
  have hshift : w ∈ (slitMap 1 '' exteriorDisk)ᶜ ↔
      w + 2 ∈ oddStarSeedOmitted 0 := by
    simp only [Set.mem_compl_iff, oddStarSeedOmitted]
    constructor
    · intro hw
      rintro ⟨z, hz, hseed⟩
      have hz0 := exterior_ne_zero hz
      have heq : oddStarSeed 0 z = slitMap 1 z + 2 := by
        rw [oddStarSeed_zero_expansion z hz0]
        simp [slitMap, div_eq_mul_inv]
        ring
      apply hw
      refine ⟨z, hz, ?_⟩
      exact add_right_cancel (heq.symm.trans hseed)
    · intro hw
      rintro ⟨z, hz, hslit⟩
      have hz0 := exterior_ne_zero hz
      have heq : oddStarSeed 0 z = slitMap 1 z + 2 := by
        rw [oddStarSeed_zero_expansion z hz0]
        simp [slitMap, div_eq_mul_inv]
        ring
      apply hw
      refine ⟨z, hz, ?_⟩
      rw [heq, hslit]
  rw [hshift, oddStarSeed_zero_omitted_eq_segment]
  change (w+2).im=0 ∧ 0≤(w+2).re ∧ (w+2).re≤4 ↔
    w.im=0 ∧ -2≤w.re ∧ w.re≤2
  simp only [Complex.add_im, Complex.add_re]
  norm_num
  intro _
  constructor <;> rintro ⟨h2,h3⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

theorem complex_square_in_four_segment_iff_real_between_two (w : ℂ) :
    (w^2).im=0 ∧ 0≤(w^2).re ∧ (w^2).re≤4 ↔
      w.im=0 ∧ -2≤w.re ∧ w.re≤2 := by
  rw [pow_two]
  simp only [Complex.mul_im, Complex.mul_re]
  constructor
  · rintro ⟨him, hlo, hhi⟩
    have him0 : w.im = 0 := by
      have hprod : w.re * w.im = 0 := by nlinarith [him]
      rcases mul_eq_zero.mp hprod with hre | him
      · have : w.im = 0 := by nlinarith [hlo, hre]
        exact this
      · exact him
    refine ⟨him0, ?_, ?_⟩ <;> nlinarith [hhi]
  · rintro ⟨him, hlo, hhi⟩
    simp only [him, mul_zero, zero_mul, sub_zero, add_zero]
    exact ⟨trivial, by nlinarith [sq_nonneg w.re], by nlinarith⟩

theorem even_slit_power_preimage_eq_regularStarPowerSet
    (k : ℕ) :
    {z : ℂ | z^k ∈ (slitMap 1 '' exteriorDisk)ᶜ} =
      regularStarPowerSet (2*k) := by
  ext z
  rw [slitMap_one_omitted_eq_segment]
  change ((z^k).im=0 ∧ -2≤(z^k).re ∧ (z^k).re≤2) ↔
    ((z^(2*k)).im=0 ∧ 0≤(z^(2*k)).re ∧ (z^(2*k)).re≤4)
  have hpow : z^(2*k) = (z^k)^2 := by
    rw [show 2*k=k*2 by omega, pow_mul]
  rw [hpow]
  exact (complex_square_in_four_segment_iff_real_between_two (z^k)).symm

end SpringerLean
