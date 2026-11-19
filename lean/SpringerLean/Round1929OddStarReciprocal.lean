import SpringerLean.Round1928OddStarSeedHolomorphic

namespace SpringerLean

noncomputable def oddStarSeedReciprocal (t : ℝ) (u : ℂ) : ℂ :=
  let s := Real.sqrt (1 - t ^ 2)
  (1 + ((s : ℂ) - (t : ℂ) * Complex.I) * u) ^ 2 /
    (1 - (t : ℂ) * Complex.I * u)

theorem oddStarSeedReciprocal_zero (t : ℝ) :
    oddStarSeedReciprocal t 0 = 1 := by
  simp [oddStarSeedReciprocal]

/-- Each of the two factors used for the analytic root lies in the
right half-plane on the open unit disk. -/
theorem oddStarSeed_reciprocal_factors_re_pos
    (t : ℝ) (ht : |t| < 1) (u : ℂ) (hu : ‖u‖ < 1) :
    0 < (1 + ((Real.sqrt (1 - t ^ 2) : ℂ) -
        (t : ℂ) * Complex.I) * u).re ∧
      0 < (1 - (t : ℂ) * Complex.I * u).re := by
  have hs := (oddStarSeed_tip_norms t ht).1
  have hs' : ‖(Real.sqrt (1 - t ^ 2) : ℂ) -
      (t : ℂ) * Complex.I‖ = 1 := by
    calc
      _ = ‖(t : ℂ) * Complex.I - Real.sqrt (1 - t ^ 2)‖ :=
        norm_sub_rev _ _
      _ = 1 := hs
  have hnum : ‖((Real.sqrt (1 - t ^ 2) : ℂ) -
      (t : ℂ) * Complex.I) * u‖ < 1 := by
    rw [norm_mul, hs', one_mul]
    exact hu
  have hden : ‖(t : ℂ) * Complex.I * u‖ < 1 := by
    have hmul : |t| * ‖u‖ ≤ |t| := by
      nlinarith [mul_nonneg (abs_nonneg t) (sub_nonneg.mpr hu.le)]
    calc
      _ = |t| * ‖u‖ := by simp [norm_mul]
      _ ≤ |t| := hmul
      _ < 1 := ht
  constructor
  · have hreal := Complex.abs_re_le_norm
      (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * u)
    change 0 < 1 +
      (((Real.sqrt (1 - t ^ 2) : ℂ) - (t : ℂ) * Complex.I) * u).re
    have hlo := (abs_le.mp hreal).1
    linarith
  · have hreal := Complex.abs_re_le_norm ((t : ℂ) * Complex.I * u)
    change 0 < 1 - ((t : ℂ) * Complex.I * u).re
    have hhi := (abs_le.mp hreal).2
    linarith

theorem oddStarSeed_reciprocal_denominator_ne_zero
    (t : ℝ) (ht : |t| < 1) (u : ℂ) (hu : ‖u‖ < 1) :
    1 - (t : ℂ) * Complex.I * u ≠ 0 := by
  intro h
  have hpos := (oddStarSeed_reciprocal_factors_re_pos t ht u hu).2
  rw [h] at hpos
  norm_num at hpos

theorem oddStarSeed_reciprocal_numerator_ne_zero
    (t : ℝ) (ht : |t| < 1) (u : ℂ) (hu : ‖u‖ < 1) :
    1 + ((Real.sqrt (1 - t ^ 2) : ℂ) -
      (t : ℂ) * Complex.I) * u ≠ 0 := by
  intro h
  have hpos := (oddStarSeed_reciprocal_factors_re_pos t ht u hu).1
  rw [h] at hpos
  norm_num at hpos

theorem oddStarSeedReciprocal_analyticOnNhd_unitDisk
    (t : ℝ) (ht : |t| < 1) :
    AnalyticOnNhd ℂ (oddStarSeedReciprocal t)
      (Metric.ball (0 : ℂ) 1) := by
  change AnalyticOnNhd ℂ
    (fun u : ℂ =>
      (1 + ((Real.sqrt (1 - t ^ 2) : ℂ) -
        (t : ℂ) * Complex.I) * u) ^ 2 /
        (1 - (t : ℂ) * Complex.I * u))
      (Metric.ball (0 : ℂ) 1)
  apply AnalyticOnNhd.div
  · fun_prop
  · fun_prop
  · intro u hu
    exact oddStarSeed_reciprocal_denominator_ne_zero t ht u
      (by simpa [Metric.mem_ball, dist_zero_right] using hu)

/-- The rational map at infinity becomes a quotient of two disk factors. -/
theorem oddStarSeed_reciprocal_identity
    (t : ℝ) (u : ℂ) (hu : u ≠ 0)
    (hden : 1 - (t : ℂ) * Complex.I * u ≠ 0) :
    u * oddStarSeed t u⁻¹ = oddStarSeedReciprocal t u := by
  unfold oddStarSeed oddStarSeedReciprocal
  field_simp [hu, hden]
  ring

end SpringerLean

#print axioms SpringerLean.oddStarSeed_reciprocal_identity
#print axioms SpringerLean.oddStarSeed_reciprocal_factors_re_pos
#print axioms SpringerLean.oddStarSeedReciprocal_analyticOnNhd_unitDisk
