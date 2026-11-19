import SpringerLean.Round138SixthPrelude

namespace SpringerLean

open PowerSeries

theorem exteriorFormalResidue_four (F : ℂ → ℂ) :
    exteriorFormalResidue F 4 =
      4 * (exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2) := by
  let f := exteriorFormalForward F
  let g := schoberActualForwardShift F
  let A : PowerSeries ℂ := PowerSeries.X ^ 2 * g
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, schoberActualForwardShift, hf0] using
      (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : formalExteriorPhi f = 1 + A := by
    rw [formalExteriorPhi, hf]
    dsimp [A]
    ring
  have hs1 : PowerSeries.coeff 5 A = exteriorForwardCoeff F 4 := by
    dsimp [A]
    rw [show 5 = 3 + 2 by omega, PowerSeries.coeff_X_pow_mul,
      schoberActualForwardShift_coeff]
  have hs2 : PowerSeries.coeff 5 (A ^ 2) =
      PowerSeries.coeff 1 (g ^ 2) := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul (g ^ 2) 4 1 using 1 <;> ring
  have hs3 : PowerSeries.coeff 5 (A ^ 3) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 3) 6 5 using 1 <;>
      ring_nf <;> norm_num
  have hs4 : PowerSeries.coeff 5 (A ^ 4) = 0 := by
    dsimp [A]
    rw [mul_pow]
    convert PowerSeries.coeff_X_pow_mul' (g ^ 4) 8 5 using 1 <;>
      ring_nf <;> norm_num
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
    rw [schoberActualForwardShift_square_coeff]
    norm_num [Finset.sum_range_succ]
    ring
  have hpow : (1 + A) ^ 4 =
      1 + 4 * A + 6 * A ^ 2 + 4 * A ^ 3 + A ^ 4 := by ring
  change PowerSeries.coeff 5 ((formalExteriorPhi f) ^ 4) = _
  rw [hphi, hpow]
  simp only [map_add, PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_ofNat_mul, hs1, hs2, hs3, hs4, hsq1]
  simp
  ring

theorem exteriorInverseCoeff_four_eq_forward
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    exteriorInverseCoeff F 4 =
      exteriorForwardCoeff F 4 +
        3 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
  have h := exteriorInverseCoeff_mul_eq_formalResidue F hc 4 (by omega)
  rw [exteriorFormalResidue_four F] at h
  exact mul_left_cancel₀ (by norm_num : (4 : ℂ) ≠ 0) h

/-- Schober's weighted area estimate (7), specialized to the actual
sixth-order linear combination. -/
theorem exteriorForwardCoeff_six_pair_sq_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖exteriorForwardCoeff F 4 +
        5 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2‖ ^ 2 ≤
      (25 * ‖exteriorForwardCoeff F 1‖ ^ 2 / 2 + 1 / 4) *
        (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) := by
  let weights : ℕ → ℂ := fun j =>
    if j = 2 then 5 * exteriorForwardCoeff F 1
    else if j = 4 then 1 else 0
  have h := exteriorForwardCoeff_weighted_linear_combination_sq_le
    F hc 4 (by omega) weights
  norm_num [weights, Finset.sum_Icc_succ_top, norm_mul] at h ⊢
  convert h using 1 <;> ring

/-- Exact real arithmetic at the sixth Schober diagonal. Here `y` will be
`‖b₁‖²`. The factorization also records strictness away from the slit
endpoint; this is an algebraic lemma, not yet the actual B₁₁ theorem. -/
theorem schober_six_diagonal_arithmetic
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (25 * y / 2 + 1 / 4) * (1 - y) +
        (2 + 3 * y) ^ 2 +
        (9 / 2) * (1 - y) + 16 * y + 1 ≤ 42 := by
  have hid : 42 - ((25 * y / 2 + 1 / 4) * (1 - y) +
        (2 + 3 * y) ^ 2 +
        (9 / 2) * (1 - y) + 16 * y + 1) =
      (1 - y) * (129 - 14 * y) / 4 := by ring
  have hp : 0 < 129 - 14 * y := by linarith
  have hmul : 0 ≤ (1 - y) * (129 - 14 * y) :=
    mul_nonneg (sub_nonneg.mpr hy1) hp.le
  linarith

theorem schober_six_diagonal_arithmetic_strict
    (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (25 * y / 2 + 1 / 4) * (1 - y) +
        (2 + 3 * y) ^ 2 +
        (9 / 2) * (1 - y) + 16 * y + 1 < 42 := by
  have hid : 42 - ((25 * y / 2 + 1 / 4) * (1 - y) +
        (2 + 3 * y) ^ 2 +
        (9 / 2) * (1 - y) + 16 * y + 1) =
      (1 - y) * (129 - 14 * y) / 4 := by ring
  have hp : 0 < 129 - 14 * y := by linarith
  have hmul : 0 < (1 - y) * (129 - 14 * y) :=
    mul_pos (sub_pos.mpr hy1) hp
  linarith

/-- The sixth diagonal's explicit parameter estimate uses only verified
finite area, weighted Cauchy--Schwarz, and the already sharp B₃ bound. -/
theorem schoberActualDiagonal_six_param_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    schoberActualDiagonal F 6 ≤
      (25 * ‖exteriorForwardCoeff F 1‖ ^ 2 / 2 + 1 / 4) *
          (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) +
        (2 + 3 * ‖exteriorForwardCoeff F 1‖ ^ 2) ^ 2 +
        (9 / 2) * (1 - ‖exteriorForwardCoeff F 1‖ ^ 2) +
        16 * ‖exteriorForwardCoeff F 1‖ ^ 2 + 1 := by
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₄ := exteriorForwardCoeff F 4
  have hB1 := exteriorInverseCoeff_one_eq_forwardCoeff_one F hc
  have hB2 := exteriorInverseCoeff_two_eq_forwardCoeff_two F hc
  have hB4 := exteriorInverseCoeff_four_eq_forward F hc
  have hfirst : exteriorInverseCoeff F 4 +
      2 * exteriorInverseCoeff F 1 * exteriorInverseCoeff F 2 =
      b₄ + 5 * b₁ * b₂ := by
    rw [hB1, hB2, hB4]
    ring
  have hpair := exteriorForwardCoeff_six_pair_sq_le F hc
  have hB3 := exteriorInverseCoeff_three_norm_le_one F hc
  let y : ℝ := ‖b₁‖ ^ 2
  have hy0 : 0 ≤ y := by positivity
  have hsecond : ‖2 * exteriorInverseCoeff F 3 +
      3 * (exteriorInverseCoeff F 1) ^ 2‖ ≤ 2 + 3 * y := by
    calc
      _ ≤ ‖(2 : ℂ) * exteriorInverseCoeff F 3‖ +
          ‖(3 : ℂ) * (exteriorInverseCoeff F 1) ^ 2‖ :=
        norm_add_le _ _
      _ = 2 * ‖exteriorInverseCoeff F 3‖ + 3 * y := by
        rw [hB1]
        simp [y, b₁, norm_mul, norm_pow]
      _ ≤ 2 + 3 * y := by linarith
  have hsecond_sq : ‖2 * exteriorInverseCoeff F 3 +
      3 * (exteriorInverseCoeff F 1) ^ 2‖ ^ 2 ≤
      (2 + 3 * y) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hsecond
  have htail := exteriorForwardCoeff_finite_area_tail F hc 2 (by omega)
  have hB2sq : 9 * ‖exteriorInverseCoeff F 2‖ ^ 2 ≤
      (9 / 2 : ℝ) * (1 - y) := by
    rw [hB2]
    norm_num [Finset.sum_Icc_succ_top, y, b₁] at htail ⊢
    linarith
  rw [hB1] at hsecond_sq
  rw [schoberActualDiagonal_six F hc, hfirst, hB1]
  dsimp [y, b₁, b₂, b₄] at hpair hsecond_sq hB2sq ⊢
  linarith

/-- Once the actual sixth tensor diagonal comparison is established, the
remaining sixth-order scalar bound and strictness follow with no new
analytic hypotheses. The diagonal comparison remains an explicit premise. -/
theorem exteriorInverseCoeff_eleven_norm_le_forty_two_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 11‖ ≤ schoberActualDiagonal F 6) :
    ‖exteriorInverseCoeff F 11‖ ≤ 42 := by
  let y : ℝ := ‖exteriorForwardCoeff F 1‖ ^ 2
  have hβ : ‖exteriorForwardCoeff F 1‖ ≤ 1 :=
    exteriorForwardCoeff_one_norm_le_of_finite_area F
      (fun N => exteriorForwardCoeff_finite_area F hc N)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 := by dsimp [y]; nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  calc
    ‖exteriorInverseCoeff F 11‖ ≤ schoberActualDiagonal F 6 := hdiag
    _ ≤ (25 * y / 2 + 1 / 4) * (1 - y) +
          (2 + 3 * y) ^ 2 + (9 / 2) * (1 - y) + 16 * y + 1 :=
      schoberActualDiagonal_six_param_le F hc
    _ ≤ 42 := schober_six_diagonal_arithmetic y hy0 hy1

theorem exteriorInverseCoeff_eleven_norm_lt_forty_two_of_diagonal
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (hdiag : ‖exteriorInverseCoeff F 11‖ ≤ schoberActualDiagonal F 6)
    (hβ : ‖exteriorForwardCoeff F 1‖ < 1) :
    ‖exteriorInverseCoeff F 11‖ < 42 := by
  let y : ℝ := ‖exteriorForwardCoeff F 1‖ ^ 2
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by dsimp [y]; nlinarith [norm_nonneg (exteriorForwardCoeff F 1)]
  calc
    ‖exteriorInverseCoeff F 11‖ ≤ schoberActualDiagonal F 6 := hdiag
    _ ≤ (25 * y / 2 + 1 / 4) * (1 - y) +
          (2 + 3 * y) ^ 2 + (9 / 2) * (1 - y) + 16 * y + 1 :=
      schoberActualDiagonal_six_param_le F hc
    _ < 42 := schober_six_diagonal_arithmetic_strict y hy0 hy1

end SpringerLean
