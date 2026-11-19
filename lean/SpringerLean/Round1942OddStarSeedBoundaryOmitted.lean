import SpringerLean.Round1941OddStarSeedSurjective

namespace SpringerLean

/-- The two preimages of a seed value are either equal or are paired by
the product of their coordinates relative to the pole. -/
theorem oddStarSeed_same_value_or_partner
    (t : ℝ) {z w : ℂ}
    (hz : z - (t : ℂ) * Complex.I ≠ 0)
    (hw : w - (t : ℂ) * Complex.I ≠ 0)
    (heq : oddStarSeed t z = oddStarSeed t w) :
    z = w ∨
      (z - (t : ℂ) * Complex.I) *
        (w - (t : ℂ) * Complex.I) =
          (Real.sqrt (1 - t ^ 2) : ℂ) ^ 2 := by
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  let u : ℂ := z - (t : ℂ) * Complex.I
  let v : ℂ := w - (t : ℂ) * Complex.I
  change (u + (s : ℂ)) ^ 2 / u =
    (v + (s : ℂ)) ^ 2 / v at heq
  have hcross := (div_eq_div_iff hz hw).mp heq
  have hfactor :
      (u + (s : ℂ)) ^ 2 * v -
        (v + (s : ℂ)) ^ 2 * u =
          (u - v) * (u * v - (s : ℂ) ^ 2) := by ring
  have hprod : (u - v) * (u * v - (s : ℂ) ^ 2) = 0 := by
    rw [← hfactor, sub_eq_zero]
    exact hcross
  rcases mul_eq_zero.mp hprod with hsame | hpartner
  · left
    have huv : u = v := sub_eq_zero.mp hsame
    dsimp [u, v] at huv
    linear_combination huv
  · right
    exact sub_eq_zero.mp hpartner

/-- A partner of a unit-circle point is another unit-circle point. -/
theorem oddStarSeed_partner_on_circle
    (t : ℝ) (ht : |t| < 1) {z w : ℂ}
    (hz : z ∈ oddStarSeedUnitCircle)
    (hprod : (z - (t : ℂ) * Complex.I) *
        (w - (t : ℂ) * Complex.I) =
          (Real.sqrt (1 - t ^ 2) : ℂ) ^ 2) :
    w ∈ oddStarSeedUnitCircle := by
  have hden := oddStarSeed_denominator_ne_zero_on_circle t ht hz
  have hq : 0 ≤ 1 - t ^ 2 := by
    rcases abs_lt.mp ht with ⟨hl, hu⟩
    nlinarith
  have hs2 : (Real.sqrt (1 - t ^ 2) : ℂ) ^ 2 =
      (1 - t ^ 2 : ℝ) := by
    exact_mod_cast Real.sq_sqrt hq
  have hwformula : w = (1 + (t : ℂ) * Complex.I * z) /
      (z - (t : ℂ) * Complex.I) := by
    apply (eq_div_iff hden).mpr
    calc
      w * (z - (t : ℂ) * Complex.I) =
          (z - (t : ℂ) * Complex.I) *
            (w - (t : ℂ) * Complex.I) +
              (t : ℂ) * Complex.I *
                (z - (t : ℂ) * Complex.I) := by ring
      _ = 1 + (t : ℂ) * Complex.I * z := by
        rw [hprod, hs2]
        push_cast
        ring_nf
        simp [Complex.I_sq]
  have hznorm : ‖z‖ = 1 := by
    simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hz
  have hdiff := oddStarSeed_partner_norm_identity t z
  have hnormeq : ‖z - (t : ℂ) * Complex.I‖ =
      ‖1 + (t : ℂ) * Complex.I * z‖ := by
    rw [hznorm] at hdiff
    norm_num at hdiff
    nlinarith [norm_nonneg (z - (t : ℂ) * Complex.I),
      norm_nonneg (1 + (t : ℂ) * Complex.I * z)]
  have hdenpos : 0 < ‖z - (t : ℂ) * Complex.I‖ := norm_pos_iff.mpr hden
  have hwnorm : ‖w‖ = 1 := by
    rw [hwformula, norm_div, ← hnormeq]
    exact div_self hdenpos.ne'
  simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hwnorm

/-- No value attained on the unit-circle boundary is attained from the
open exterior disk. -/
theorem oddStarSeed_boundary_image_subset_omitted
    (t : ℝ) (ht : |t| < 1) :
    oddStarSeed t '' oddStarSeedUnitCircle ⊆ oddStarSeedOmitted t := by
  rintro y ⟨z, hz, rfl⟩ himage
  obtain ⟨w, hw, heq⟩ := himage
  have hdenz := oddStarSeed_denominator_ne_zero_on_circle t ht hz
  have hdenw := oddStarSeed_denominator_ne_zero t ht w hw
  rcases oddStarSeed_same_value_or_partner t hdenz hdenw heq.symm with
    hsame | hpartner
  · have hznorm : ‖z‖ = 1 := by
      simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hz
    have hwnorm : 1 < ‖w‖ := hw
    rw [← hsame, hznorm] at hwnorm
    linarith
  · have hcircle := oddStarSeed_partner_on_circle t ht hz hpartner
    have hwnorm : ‖w‖ = 1 := by
      simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using hcircle
    have hwext : 1 < ‖w‖ := hw
    linarith

end SpringerLean

#print axioms SpringerLean.oddStarSeed_boundary_image_subset_omitted
