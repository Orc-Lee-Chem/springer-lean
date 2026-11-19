import SpringerLean.Round76FaberTwo

set_option maxHeartbeats 500000

namespace SpringerLean

open PowerSeries

/-- The first three negative modes of the third Faber polynomial.
The constant correction in that polynomial has no negative modes. -/
theorem formalFaberThree_first_three_negative_modes
    (F : ℂ → ℂ) :
    let φ := formalExteriorPhi (exteriorFormalForward F)
    let b1 := exteriorForwardCoeff F 1
    PowerSeries.coeff 4 (φ ^ 3) - 3 * b1 * PowerSeries.coeff 2 φ =
      3 * exteriorForwardCoeff F 3 ∧
    PowerSeries.coeff 5 (φ ^ 3) - 3 * b1 * PowerSeries.coeff 3 φ =
      3 * (exteriorForwardCoeff F 4 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2) ∧
    PowerSeries.coeff 6 (φ ^ 3) - 3 * b1 * PowerSeries.coeff 4 φ =
      3 * (exteriorForwardCoeff F 5 +
        exteriorForwardCoeff F 1 * exteriorForwardCoeff F 3 +
        (exteriorForwardCoeff F 2) ^ 2) +
        (exteriorForwardCoeff F 1) ^ 3 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  let φ := formalExteriorPhi f
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : φ = 1 + PowerSeries.X ^ 2 * g := by
    change formalExteriorPhi f = _
    rw [formalExteriorPhi, hf]
    ring
  have hpow : (1 + PowerSeries.X ^ 2 * g) ^ 3 =
      1 + 3 * (PowerSeries.X ^ 2 * g) +
        3 * (PowerSeries.X ^ 4 * (g ^ 2)) +
        PowerSeries.X ^ 6 * (g ^ 3) := by ring
  have hg0 : PowerSeries.coeff 0 g = exteriorForwardCoeff F 1 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg1 : PowerSeries.coeff 1 g = exteriorForwardCoeff F 2 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = exteriorForwardCoeff F 3 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 3
  have hg3 : PowerSeries.coeff 3 g = exteriorForwardCoeff F 4 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 4
  have hg4 : PowerSeries.coeff 4 g = exteriorForwardCoeff F 5 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 5
  have hsq0 : PowerSeries.coeff 0 (g ^ 2) = (PowerSeries.coeff 0 g) ^ 2 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff]
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hsq2 : PowerSeries.coeff 2 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 2 g +
        (PowerSeries.coeff 1 g) ^ 2 := by
    rw [pow_two, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_num [Finset.sum_range_succ]
    ring
  have hcube0 : PowerSeries.coeff 0 (g ^ 3) =
      (PowerSeries.coeff 0 g) ^ 3 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff]
  have hsφ2 : PowerSeries.coeff 2 φ = PowerSeries.coeff 0 g := by
    rw [hphi]
    simpa using PowerSeries.coeff_X_pow_mul g 2 0
  have hsφ3 : PowerSeries.coeff 3 φ = PowerSeries.coeff 1 g := by
    rw [hphi]
    simpa using PowerSeries.coeff_X_pow_mul g 2 1
  have hsφ4 : PowerSeries.coeff 4 φ = PowerSeries.coeff 2 g := by
    rw [hphi]
    simpa using PowerSeries.coeff_X_pow_mul g 2 2
  have h4a : PowerSeries.coeff 4 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 2 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 2
  have h5a : PowerSeries.coeff 5 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 3 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 3
  have h6a : PowerSeries.coeff 6 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 4 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 4
  have h4b : PowerSeries.coeff 4 (PowerSeries.X ^ 4 * (g ^ 2)) =
      PowerSeries.coeff 0 (g ^ 2) := by
    simpa only [Nat.zero_add] using PowerSeries.coeff_X_pow_mul (g ^ 2) 4 0
  have h5b : PowerSeries.coeff 5 (PowerSeries.X ^ 4 * (g ^ 2)) =
      PowerSeries.coeff 1 (g ^ 2) := by
    simpa only using PowerSeries.coeff_X_pow_mul (g ^ 2) 4 1
  have h6b : PowerSeries.coeff 6 (PowerSeries.X ^ 4 * (g ^ 2)) =
      PowerSeries.coeff 2 (g ^ 2) := by
    simpa only using PowerSeries.coeff_X_pow_mul (g ^ 2) 4 2
  have h4c : PowerSeries.coeff 4 (PowerSeries.X ^ 6 * (g ^ 3)) = 0 := by
    simpa using PowerSeries.coeff_X_pow_mul' (g ^ 3) 6 4
  have h5c : PowerSeries.coeff 5 (PowerSeries.X ^ 6 * (g ^ 3)) = 0 := by
    simpa using PowerSeries.coeff_X_pow_mul' (g ^ 3) 6 5
  have h6c : PowerSeries.coeff 6 (PowerSeries.X ^ 6 * (g ^ 3)) =
      PowerSeries.coeff 0 (g ^ 3) := by
    simpa only [Nat.zero_add] using PowerSeries.coeff_X_pow_mul (g ^ 3) 6 0
  dsimp
  constructor
  · change PowerSeries.coeff 4 (φ ^ 3) -
      3 * exteriorForwardCoeff F 1 * PowerSeries.coeff 2 φ = _
    rw [hsφ2, hphi, hpow]
    simp [hsφ2, h4a, h4b, h4c, hsq0, hg0, hg2]
    ring
  constructor
  · change PowerSeries.coeff 5 (φ ^ 3) -
      3 * exteriorForwardCoeff F 1 * PowerSeries.coeff 3 φ = _
    rw [hsφ3, hphi, hpow]
    simp [hsφ3, h5a, h5b, h5c, hsq1, hg0, hg1, hg3]
    ring
  · change PowerSeries.coeff 6 (φ ^ 3) -
      3 * exteriorForwardCoeff F 1 * PowerSeries.coeff 4 φ = _
    rw [hsφ4, hphi, hpow]
    simp [hsφ4, h6a, h6b, h6c, hsq2, hcube0, hg0, hg1, hg2, hg4]
    ring

/-- All three negative modes of the third Faber polynomial coincide with
three times the third row of the finite logarithmic coefficient kernel. -/
theorem formalFaberThree_modes_eq_logKernel
    (F : ℂ → ℂ) :
    let φ := formalExteriorPhi (exteriorFormalForward F)
    let b1 := exteriorForwardCoeff F 1
    let b2 := exteriorForwardCoeff F 2
    let b3 := exteriorForwardCoeff F 3
    let b4 := exteriorForwardCoeff F 4
    let b5 := exteriorForwardCoeff F 5
    PowerSeries.coeff 4 (φ ^ 3) - 3 * b1 * PowerSeries.coeff 2 φ =
      3 * schoberBiCoeff 3 1 (schoberKernelQ3 b1 b2 b3 b4 b5) ∧
    PowerSeries.coeff 5 (φ ^ 3) - 3 * b1 * PowerSeries.coeff 3 φ =
      3 * schoberBiCoeff 3 2 (schoberKernelQ3 b1 b2 b3 b4 b5) ∧
    PowerSeries.coeff 6 (φ ^ 3) - 3 * b1 * PowerSeries.coeff 4 φ =
      3 * schoberBiCoeff 3 3 (schoberKernelQ3 b1 b2 b3 b4 b5) := by
  rcases formalFaberThree_first_three_negative_modes F with ⟨h1,h2,h3⟩
  dsimp
  constructor
  · rw [h1, schoberKernelQ3_coeff_three_one]
  constructor
  · rw [h2, schoberKernelQ3_coeff_three_two]
  · rw [h3, schoberKernelQ3_coeff_three_three]
    simp [schoberQ33]
    ring

end SpringerLean
