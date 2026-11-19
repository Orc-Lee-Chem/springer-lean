import SpringerLean.Round94FourthLimit

set_option maxHeartbeats 500000

namespace SpringerLean

open PowerSeries

noncomputable def fourthFaberFormalFactor (F : ℂ → ℂ) : PowerSeries ℂ :=
  let φ := formalExteriorPhi (exteriorFormalForward F)
  φ ^ 4 -
    PowerSeries.C (4 * exteriorForwardCoeff F 1) * PowerSeries.X ^ 2 * φ ^ 2 -
    PowerSeries.C (4 * exteriorForwardCoeff F 2) * PowerSeries.X ^ 3 * φ -
    PowerSeries.C (4 * exteriorForwardCoeff F 3 -
      2 * (exteriorForwardCoeff F 1) ^ 2) * PowerSeries.X ^ 4

/-- The finite fourth-Faber expansion needed to read negative modes through
order four. The shifted forward series has coefficients `b_(j+1)`. -/
theorem fourthFaberFormalFactor_expand (F : ℂ → ℂ) :
    let f := exteriorFormalForward F
    let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
    fourthFaberFormalFactor F =
      1 + PowerSeries.X ^ 2 *
          (4 * g - PowerSeries.C (4 * exteriorForwardCoeff F 1)) -
        PowerSeries.X ^ 3 * PowerSeries.C (4 * exteriorForwardCoeff F 2) +
        PowerSeries.X ^ 4 *
          (6 * g ^ 2 - 2 * PowerSeries.C (4 * exteriorForwardCoeff F 1) * g -
            PowerSeries.C (4 * exteriorForwardCoeff F 3 -
              2 * (exteriorForwardCoeff F 1) ^ 2)) -
        PowerSeries.X ^ 5 *
          (PowerSeries.C (4 * exteriorForwardCoeff F 2) * g) +
        PowerSeries.X ^ 6 *
          (4 * g ^ 3 - PowerSeries.C (4 * exteriorForwardCoeff F 1) * g ^ 2) +
        PowerSeries.X ^ 8 * g ^ 4 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hφ : formalExteriorPhi f = 1 + PowerSeries.X ^ 2 * g := by
    rw [formalExteriorPhi, hf]
    ring
  dsimp only [fourthFaberFormalFactor]
  rw [hφ]
  ring

/-- Coefficient of the order-two term of the shifted-square series. -/
theorem fourthFaber_shifted_square_coeff_two (g : PowerSeries ℂ) :
    PowerSeries.coeff 2 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 2 g +
        (PowerSeries.coeff 1 g) ^ 2 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

/-- All constant scalar coefficients in the fourth-row formulas can be
collected inside the `PowerSeries.C` ring homomorphism. -/
theorem fourthFaber_two_C_four (b : ℂ) :
    (2 : PowerSeries ℂ) * PowerSeries.C (4 * b) =
      PowerSeries.C (8 * b) := by
  have htwo : (2 : PowerSeries ℂ) = PowerSeries.C (2 : ℂ) := by
    calc
      (2 : PowerSeries ℂ) = 1 + 1 := by norm_num
      _ = PowerSeries.C (1 + 1 : ℂ) := by rw [map_add, map_one]
      _ = PowerSeries.C (2 : ℂ) := by norm_num
  rw [htwo, ← map_mul]
  congr 1
  ring

/-- The second negative fourth-Faber mode. This is an exact polynomial
identity in the original map's actual forward coefficients. -/
theorem fourthFaberFormalFactor_coeff_six (F : ℂ → ℂ) :
    PowerSeries.coeff 6 (fourthFaberFormalFactor F) =
      4 * exteriorForwardCoeff F 5 +
      4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      2 * (exteriorForwardCoeff F 2) ^ 2 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  have hg0 : PowerSeries.coeff 0 g = b₁ := by
    simpa [g, f, b₁, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg0' : PowerSeries.constantCoeff g = b₁ := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [g, f, b₂, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = b₃ := by
    simpa [g, f, b₃, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 3
  have hg4 : PowerSeries.coeff 4 g = exteriorForwardCoeff F 5 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 5
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  have hsq0 : PowerSeries.constantCoeff (g ^ 2) = b₁ ^ 2 := by
    simp [hg0']
  have hcube0 : PowerSeries.constantCoeff (g ^ 3) = b₁ ^ 3 := by
    simp [hg0']
  rw [fourthFaberFormalFactor_expand F]
  change PowerSeries.coeff 6
    (1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
      PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
      PowerSeries.X ^ 4 *
        (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
          PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2)) -
      PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
      PowerSeries.X ^ 6 *
        (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
      PowerSeries.X ^ 8 * g ^ 4) = _
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num
  have hterm : PowerSeries.coeff 2
      ((2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g) =
        8 * b₁ * b₃ := by
    have heq : (2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g =
        PowerSeries.C (8 * b₁) * g := by
      calc
        (2 : PowerSeries ℂ) *
            (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g =
            (2 : PowerSeries ℂ) * PowerSeries.C (4 * b₁) * g := by
              rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
                PowerSeries.C (4 * b₁) by rw [map_mul]]
        _ = PowerSeries.C (8 * b₁) * g := by
              rw [fourthFaber_two_C_four]
    rw [heq, PowerSeries.coeff_C_mul, hg2]
  have hzero : PowerSeries.coeff 2 ((PowerSeries.C b₁) ^ 2) = 0 := by
    simp [pow_two]
  have hterm₂ : PowerSeries.coeff 1
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ * g) =
      4 * b₂ ^ 2 := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ =
      PowerSeries.C (4 * b₂) by rw [map_mul],
      PowerSeries.coeff_C_mul, hg1]
    ring
  rw [hterm, hzero, hterm₂, hsq2, hg0, hg1, hg2, hg4,
    hg0']
  ring

/-- The same second negative fourth-Faber mode, now read from the Taylor
derivatives of the genuine analytic exterior forward germ. -/
theorem fourthFaberFactor_actual_mode_six
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 6 =
      4 * exteriorForwardCoeff F 5 +
      4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
      2 * (exteriorForwardCoeff F 2) ^ 2 := by
  rw [← actualTaylorSeries_coeff]
  have h := fourthFaberFactor_actualTaylorSeries F hc
  change actualTaylorSeries (fourthFaberFactor F) = _ at h
  rw [h]
  exact fourthFaberFormalFactor_coeff_six F

theorem fourthFaber_shifted_square_coeff_three (g : PowerSeries ℂ) :
    PowerSeries.coeff 3 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 3 g +
        2 * PowerSeries.coeff 1 g * PowerSeries.coeff 2 g := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

theorem fourthFaber_shifted_cube_coeff_one (g : PowerSeries ℂ) :
    PowerSeries.coeff 1 (g ^ 3) =
      3 * (PowerSeries.coeff 0 g) ^ 2 * PowerSeries.coeff 1 g := by
  rw [PowerSeries.coeff_one_pow]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

/-- Third negative fourth-Faber mode, still using the original actual
forward coefficient sequence. -/
theorem fourthFaberFormalFactor_coeff_seven (F : ℂ → ℂ) :
    PowerSeries.coeff 7 (fourthFaberFormalFactor F) =
      4 * exteriorForwardCoeff F 6 +
      4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 +
      4 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 2 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  have hg0 : PowerSeries.coeff 0 g = b₁ := by
    simpa [g, f, b₁, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [g, f, b₂, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = b₃ := by
    simpa [g, f, b₃, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 3
  have hg3 : PowerSeries.coeff 3 g = exteriorForwardCoeff F 4 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 4
  have hg5 : PowerSeries.coeff 5 g = exteriorForwardCoeff F 6 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 6
  have hsq3 := fourthFaber_shifted_square_coeff_three g
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hcube1 := fourthFaber_shifted_cube_coeff_one g
  rw [fourthFaberFormalFactor_expand F]
  change PowerSeries.coeff 7
    (1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
      PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
      PowerSeries.X ^ 4 *
        (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
          PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2)) -
      PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
      PowerSeries.X ^ 6 *
        (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
      PowerSeries.X ^ 8 * g ^ 4) = _
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num
  have hterm₁ : PowerSeries.coeff 3
      ((2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g) =
        8 * b₁ * exteriorForwardCoeff F 4 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g =
          PowerSeries.C (8 * b₁) * g by
      rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
        PowerSeries.C (4 * b₁) by rw [map_mul], fourthFaber_two_C_four],
      PowerSeries.coeff_C_mul, hg3]
  have hterm₂ : PowerSeries.coeff 2
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ * g) =
        4 * b₂ * b₃ := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ =
      PowerSeries.C (4 * b₂) by rw [map_mul],
      PowerSeries.coeff_C_mul, hg2]
  have hterm₃ : PowerSeries.coeff 1
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ * g ^ 2) =
        4 * b₁ * (2 * b₁ * b₂) := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
      PowerSeries.C (4 * b₁) by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq1, hg0, hg1]
  have hzero : PowerSeries.coeff 3 ((PowerSeries.C b₁) ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hzero,
    hsq3, hcube1, hg0, hg1, hg2, hg3, hg5]
  ring

theorem fourthFaberFactor_actual_mode_seven
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 7 =
      4 * exteriorForwardCoeff F 6 +
      4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
      8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 +
      4 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 2 := by
  rw [← actualTaylorSeries_coeff]
  have h := fourthFaberFactor_actualTaylorSeries F hc
  change actualTaylorSeries (fourthFaberFactor F) = _ at h
  rw [h]
  exact fourthFaberFormalFactor_coeff_seven F

theorem fourthFaber_shifted_square_coeff_four (g : PowerSeries ℂ) :
    PowerSeries.coeff 4 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 4 g +
        2 * PowerSeries.coeff 1 g * PowerSeries.coeff 3 g +
        (PowerSeries.coeff 2 g) ^ 2 := by
  rw [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  ring

theorem fourthFaber_shifted_cube_coeff_two (g : PowerSeries ℂ) :
    PowerSeries.coeff 2 (g ^ 3) =
      3 * (PowerSeries.coeff 0 g) ^ 2 * PowerSeries.coeff 2 g +
        3 * PowerSeries.coeff 0 g * (PowerSeries.coeff 1 g) ^ 2 := by
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  rw [show g ^ 3 = g ^ 2 * g by ring, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff] at hsq1 hsq2
  rw [hsq1, hsq2]
  ring

/-- Fourth negative fourth-Faber mode. This finishes the finite coefficient
table for the degree-four Faber polynomial itself. -/
theorem fourthFaberFormalFactor_coeff_eight (F : ℂ → ℂ) :
    PowerSeries.coeff 8 (fourthFaberFormalFactor F) =
      4 * exteriorForwardCoeff F 7 +
      4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      6 * (exteriorForwardCoeff F 3) ^ 2 +
      4 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 3 +
      8 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 2) ^ 2 +
      (exteriorForwardCoeff F 1) ^ 4 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let b₁ := exteriorForwardCoeff F 1
  let b₂ := exteriorForwardCoeff F 2
  let b₃ := exteriorForwardCoeff F 3
  have hg0 : PowerSeries.coeff 0 g = b₁ := by
    simpa [g, f, b₁, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg0' : PowerSeries.constantCoeff g = b₁ := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hg0
  have hg1 : PowerSeries.coeff 1 g = b₂ := by
    simpa [g, f, b₂, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = b₃ := by
    simpa [g, f, b₃, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 3
  have hg3 : PowerSeries.coeff 3 g = exteriorForwardCoeff F 4 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 4
  have hg4 : PowerSeries.coeff 4 g = exteriorForwardCoeff F 5 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 5
  have hg6 : PowerSeries.coeff 6 g = exteriorForwardCoeff F 7 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 7
  have hsq4 := fourthFaber_shifted_square_coeff_four g
  have hsq2 := fourthFaber_shifted_square_coeff_two g
  have hcube2 := fourthFaber_shifted_cube_coeff_two g
  rw [fourthFaberFormalFactor_expand F]
  change PowerSeries.coeff 8
    (1 + PowerSeries.X ^ 2 * (4 * g - PowerSeries.C (4 * b₁)) -
      PowerSeries.X ^ 3 * PowerSeries.C (4 * b₂) +
      PowerSeries.X ^ 4 *
        (6 * g ^ 2 - 2 * PowerSeries.C (4 * b₁) * g -
          PowerSeries.C (4 * b₃ - 2 * b₁ ^ 2)) -
      PowerSeries.X ^ 5 * (PowerSeries.C (4 * b₂) * g) +
      PowerSeries.X ^ 6 *
        (4 * g ^ 3 - PowerSeries.C (4 * b₁) * g ^ 2) +
      PowerSeries.X ^ 8 * g ^ 4) = _
  simp only [map_add, map_sub, PowerSeries.coeff_X_pow_mul']
  norm_num
  have hterm₁ : PowerSeries.coeff 4
      ((2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g) =
        8 * b₁ * exteriorForwardCoeff F 5 := by
    rw [show (2 : PowerSeries ℂ) *
        (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁) * g =
          PowerSeries.C (8 * b₁) * g by
      rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
        PowerSeries.C (4 * b₁) by rw [map_mul], fourthFaber_two_C_four],
      PowerSeries.coeff_C_mul, hg4]
  have hterm₂ : PowerSeries.coeff 3
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ * g) =
        4 * b₂ * exteriorForwardCoeff F 4 := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₂ =
      PowerSeries.C (4 * b₂) by rw [map_mul],
      PowerSeries.coeff_C_mul, hg3]
  have hterm₃ : PowerSeries.coeff 2
      (PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ * g ^ 2) =
        4 * b₁ * (2 * b₁ * b₃ + b₂ ^ 2) := by
    rw [show PowerSeries.C (4 : ℂ) * PowerSeries.C b₁ =
      PowerSeries.C (4 * b₁) by rw [map_mul],
      PowerSeries.coeff_C_mul, hsq2, hg0, hg1, hg2]
  have hzero : PowerSeries.coeff 4 ((PowerSeries.C b₁) ^ 2) = 0 := by
    simp [pow_two]
  rw [hterm₁, hterm₂, hterm₃, hzero,
    hsq4, hcube2, hg0, hg1, hg2, hg3, hg4, hg6, hg0']
  ring

theorem fourthFaberFactor_actual_mode_eight
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    actualTaylorCoeff (fourthFaberFactor F) 8 =
      4 * exteriorForwardCoeff F 7 +
      4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
      8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
      6 * (exteriorForwardCoeff F 3) ^ 2 +
      4 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 3 +
      8 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 2) ^ 2 +
      (exteriorForwardCoeff F 1) ^ 4 := by
  rw [← actualTaylorSeries_coeff]
  have h := fourthFaberFactor_actualTaylorSeries F hc
  change actualTaylorSeries (fourthFaberFactor F) = _ at h
  rw [h]
  exact fourthFaberFormalFactor_coeff_eight F

/-- The original map's fourth Faber row as an explicit finite polynomial
inequality in the same forward Laurent coefficients `b₁,…,b₇`. This is a
one-row consequence of actual univalence, not yet the full 4×4 contraction. -/
theorem exterior_fourthFaber_forward_row_energy_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ‖4 * exteriorForwardCoeff F 4‖ ^ 2 +
        2 * ‖4 * exteriorForwardCoeff F 5 +
          4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
          2 * (exteriorForwardCoeff F 2) ^ 2‖ ^ 2 +
        3 * ‖4 * exteriorForwardCoeff F 6 +
          4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 4 +
          8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 3 +
          4 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 2‖ ^ 2 +
        4 * ‖4 * exteriorForwardCoeff F 7 +
          4 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 5 +
          8 * exteriorForwardCoeff F 2 * exteriorForwardCoeff F 4 +
          6 * (exteriorForwardCoeff F 3) ^ 2 +
          4 * (exteriorForwardCoeff F 1) ^ 2 * exteriorForwardCoeff F 3 +
          8 * exteriorForwardCoeff F 1 * (exteriorForwardCoeff F 2) ^ 2 +
          (exteriorForwardCoeff F 1) ^ 4‖ ^ 2 ≤ 4 := by
  have h := exterior_fourthFaber_actual_mode_energy_le F hc
  have h5 := fourthFaberFactor_actual_mode_five F hc
  change actualTaylorCoeff (fourthFaberFactor F) 5 =
    4 * exteriorForwardCoeff F 4 at h5
  rw [h5, fourthFaberFactor_actual_mode_six F hc,
    fourthFaberFactor_actual_mode_seven F hc,
    fourthFaberFactor_actual_mode_eight F hc] at h
  exact h

end SpringerLean
