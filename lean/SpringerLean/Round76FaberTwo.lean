import SpringerLean.Round75DiagonalRows

set_option maxHeartbeats 800000

namespace SpringerLean

open PowerSeries

/-- The first three negative modes of the second Faber polynomial after
composition with the forward series of the actual map. -/
theorem formalFaberTwo_first_three_negative_modes
    (F : ℂ → ℂ) :
    PowerSeries.coeff 3
      ((formalExteriorPhi (exteriorFormalForward F)) ^ 2) =
        2 * exteriorForwardCoeff F 2 ∧
    PowerSeries.coeff 4
      ((formalExteriorPhi (exteriorFormalForward F)) ^ 2) =
        2 * exteriorForwardCoeff F 3 +
          (exteriorForwardCoeff F 1) ^ 2 ∧
    PowerSeries.coeff 5
      ((formalExteriorPhi (exteriorFormalForward F)) ^ 2) =
        2 * exteriorForwardCoeff F 4 +
          2 * exteriorForwardCoeff F 1 * exteriorForwardCoeff F 2 := by
  let f := exteriorFormalForward F
  let g := PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) f)
  have hf0 : PowerSeries.constantCoeff f = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
      exteriorFormalForward_coeff_zero F
  have hf : f = PowerSeries.X * g := by
    simpa [g, hf0] using (PowerSeries.eq_X_mul_shift_add_const f)
  have hphi : formalExteriorPhi f = 1 + PowerSeries.X ^ 2 * g := by
    rw [formalExteriorPhi, hf]
    ring
  have hpow : (1 + PowerSeries.X ^ 2 * g) ^ 2 =
      1 + 2 * (PowerSeries.X ^ 2 * g) +
        PowerSeries.X ^ 4 * (g ^ 2) := by ring
  have hg0 : PowerSeries.coeff 0 g = exteriorForwardCoeff F 1 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 1
  have hg1 : PowerSeries.coeff 1 g = exteriorForwardCoeff F 2 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 2
  have hg2 : PowerSeries.coeff 2 g = exteriorForwardCoeff F 3 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 3
  have hg3 : PowerSeries.coeff 3 g = exteriorForwardCoeff F 4 := by
    simpa [g, f, PowerSeries.coeff_mk] using exteriorFormalForward_coeff F 4
  have hsq0 : PowerSeries.coeff 0 (g ^ 2) = (PowerSeries.coeff 0 g) ^ 2 := by
    simp [PowerSeries.coeff_zero_eq_constantCoeff]
  have hsq1 : PowerSeries.coeff 1 (g ^ 2) =
      2 * PowerSeries.coeff 0 g * PowerSeries.coeff 1 g := by
    rw [pow_two, PowerSeries.coeff_one_mul]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff]
    ring
  have hs3 : PowerSeries.coeff 3 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 1 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 1
  have hs4 : PowerSeries.coeff 4 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 2 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 2
  have hs5 : PowerSeries.coeff 5 (PowerSeries.X ^ 2 * g) =
      PowerSeries.coeff 3 g := by
    simpa using PowerSeries.coeff_X_pow_mul g 2 3
  have hq3 : PowerSeries.coeff 3 (PowerSeries.X ^ 4 * (g ^ 2)) = 0 := by
    simpa using PowerSeries.coeff_X_pow_mul' (g ^ 2) 4 3
  have hq4 : PowerSeries.coeff 4 (PowerSeries.X ^ 4 * (g ^ 2)) =
      PowerSeries.coeff 0 (g ^ 2) := by
    simpa only [Nat.zero_add] using PowerSeries.coeff_X_pow_mul (g ^ 2) 4 0
  have hq5 : PowerSeries.coeff 5 (PowerSeries.X ^ 4 * (g ^ 2)) =
      PowerSeries.coeff 1 (g ^ 2) := by
    simpa only using PowerSeries.coeff_X_pow_mul (g ^ 2) 4 1
  constructor
  · change PowerSeries.coeff 3 ((formalExteriorPhi f) ^ 2) = _
    rw [hphi, hpow]
    simp [hs3, hq3, hg1]
  constructor
  · change PowerSeries.coeff 4 ((formalExteriorPhi f) ^ 2) = _
    rw [hphi, hpow]
    simp [hs4, hq4, hsq0, hg0, hg2]
  · change PowerSeries.coeff 5 ((formalExteriorPhi f) ^ 2) = _
    rw [hphi, hpow]
    simp [hs5, hq5, hsq1, hg0, hg1, hg3]

/-- The three negative modes of the second Faber polynomial equal twice
the corresponding logarithmic kernel coefficients. -/
theorem formalFaberTwo_modes_eq_logKernel
    (F : ℂ → ℂ) :
    let b1 := exteriorForwardCoeff F 1
    let b2 := exteriorForwardCoeff F 2
    let b3 := exteriorForwardCoeff F 3
    let b4 := exteriorForwardCoeff F 4
    let b5 := exteriorForwardCoeff F 5
    PowerSeries.coeff 3
      ((formalExteriorPhi (exteriorFormalForward F)) ^ 2) =
        2 * schoberBiCoeff 2 1 (schoberKernelQ3 b1 b2 b3 b4 b5) ∧
    PowerSeries.coeff 4
      ((formalExteriorPhi (exteriorFormalForward F)) ^ 2) =
        2 * schoberBiCoeff 2 2 (schoberKernelQ3 b1 b2 b3 b4 b5) ∧
    PowerSeries.coeff 5
      ((formalExteriorPhi (exteriorFormalForward F)) ^ 2) =
        2 * schoberBiCoeff 2 3 (schoberKernelQ3 b1 b2 b3 b4 b5) := by
  rcases formalFaberTwo_first_three_negative_modes F with ⟨h1, h2, h3⟩
  dsimp
  constructor
  · rw [h1, schoberKernelQ3_coeff_two_one]
  constructor
  · rw [h2, schoberKernelQ3_coeff_two_two]
    simp [schoberQ22]
    ring
  · rw [h3, schoberKernelQ3_coeff_two_three]
    ring

end SpringerLean
