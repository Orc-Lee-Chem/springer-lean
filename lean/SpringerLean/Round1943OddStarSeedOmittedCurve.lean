import SpringerLean.Round1942OddStarSeedBoundaryOmitted

namespace SpringerLean

/-- Every interior preimage of a seed value is paired with an exterior
preimage of the same value. -/
theorem oddStarSeed_interior_partner_exterior
    (t : ℝ) (ht : |t| < 1) {z : ℂ}
    (hpole : z ≠ (t : ℂ) * Complex.I) (hz : ‖z‖ < 1) :
    ∃ w ∈ exteriorDisk, oddStarSeed t w = oddStarSeed t z := by
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  let u : ℂ := z - (t : ℂ) * Complex.I
  let v : ℂ := (s : ℂ) ^ 2 / u
  let w : ℂ := v + (t : ℂ) * Complex.I
  have hu : u ≠ 0 := sub_ne_zero.mpr hpole
  have hspos : 0 < s := oddStarSeed_sqrt_pos t ht
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
  have hv : v ≠ 0 := div_ne_zero (pow_ne_zero _ hsc) hu
  have hprod : u * v = (s : ℂ) ^ 2 := by
    dsimp [v]
    field_simp
  have hq : 0 ≤ 1 - t ^ 2 := by
    rcases abs_lt.mp ht with ⟨hl, hr⟩
    nlinarith
  have hs2 : (s : ℂ) ^ 2 = (1 - t ^ 2 : ℝ) := by
    exact_mod_cast Real.sq_sqrt hq
  have hwformula : w = (1 + (t : ℂ) * Complex.I * z) / u := by
    apply (eq_div_iff hu).mpr
    calc
      w * u = u * v + (t : ℂ) * Complex.I * u := by
        dsimp [w]
        ring
      _ = 1 + (t : ℂ) * Complex.I * z := by
        rw [hprod, hs2]
        dsimp [u]
        push_cast
        ring_nf
        simp [Complex.I_sq]
  have hdiff := oddStarSeed_partner_norm_identity t z
  have hcoef : 0 < 1 - t ^ 2 := by
    rcases abs_lt.mp ht with ⟨hl, hr⟩
    nlinarith
  have hzsq : ‖z‖ ^ 2 - 1 < 0 := by
    nlinarith [norm_nonneg z]
  have hnum : ‖u‖ < ‖1 + (t : ℂ) * Complex.I * z‖ := by
    dsimp [u]
    have hneg : (1 - t ^ 2) * (‖z‖ ^ 2 - 1) < 0 :=
      mul_neg_of_pos_of_neg hcoef hzsq
    nlinarith [norm_nonneg (z - (t : ℂ) * Complex.I),
      norm_nonneg (1 + (t : ℂ) * Complex.I * z)]
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hwext : w ∈ exteriorDisk := by
    change 1 < ‖w‖
    rw [hwformula, norm_div]
    exact (one_lt_div hupos).mpr hnum
  refine ⟨w, hwext, ?_⟩
  have hcross : (v + (s : ℂ)) ^ 2 * u =
      (u + (s : ℂ)) ^ 2 * v := by
    have hfactor :
        (v + (s : ℂ)) ^ 2 * u -
          (u + (s : ℂ)) ^ 2 * v =
            (v - u) * (u * v - (s : ℂ) ^ 2) := by ring
    apply sub_eq_zero.mp
    rw [hfactor, hprod]
    ring
  have hwsub : w - (t : ℂ) * Complex.I = v := by
    dsimp [w]
    ring
  unfold oddStarSeed
  simp only [hwsub]
  change (v + (s : ℂ)) ^ 2 / v =
    (u + (s : ℂ)) ^ 2 / u
  exact (div_eq_div_iff hv hu).mpr hcross

/-- The omitted set of the rational seed is exactly its connected
unit-circle boundary curve. -/
theorem oddStarSeed_omitted_eq_boundary_image
    (t : ℝ) (ht : |t| < 1) :
    oddStarSeedOmitted t =
      oddStarSeed t '' oddStarSeedUnitCircle := by
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨z, hpole, hG⟩ := oddStarSeed_exists_preimage t ht y
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · obtain ⟨w, hw, hsame⟩ :=
        oddStarSeed_interior_partner_exterior t ht hpole hlt
      exact False.elim (hy ⟨w, hw, hsame.trans hG⟩)
    · refine ⟨z, ?_, hG⟩
      simpa [oddStarSeedUnitCircle, Metric.mem_sphere, dist_zero_right] using heq
    · exact False.elim (hy ⟨z, hgt, hG⟩)
  · exact oddStarSeed_boundary_image_subset_omitted t ht

/-- The actual seed omitted set is a connected compact continuum and
contains both endpoints of the perturbation arc. -/
theorem oddStarSeed_omitted_connected
    (t : ℝ) (ht : |t| < 1) :
    IsConnected (oddStarSeedOmitted t) := by
  rw [oddStarSeed_omitted_eq_boundary_image t ht]
  exact oddStarSeed_boundary_image_connected t ht

end SpringerLean

#print axioms SpringerLean.oddStarSeed_interior_partner_exterior
#print axioms SpringerLean.oddStarSeed_omitted_eq_boundary_image
#print axioms SpringerLean.oddStarSeed_omitted_connected
