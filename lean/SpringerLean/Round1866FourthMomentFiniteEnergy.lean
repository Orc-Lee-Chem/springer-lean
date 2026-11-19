import SpringerLean.Round353RadialEvenPrelude

open PowerSeries

namespace SpringerLean

theorem formalPhi_square_first_coefficients (F : ℂ → ℂ) :
    let φ := formalExteriorPhi (exteriorFormalForward F)
    PowerSeries.coeff 0 (φ ^ 2) = 1 ∧
      PowerSeries.coeff 1 (φ ^ 2) = 0 ∧
      PowerSeries.coeff 2 (φ ^ 2) = 2 * exteriorForwardCoeff F 1 ∧
      PowerSeries.coeff 3 (φ ^ 2) = 2 * exteriorForwardCoeff F 2 := by
  let φ := formalExteriorPhi (exteriorFormalForward F)
  have h0 : PowerSeries.coeff 0 φ = 1 := by simp [φ, formalExteriorPhi]
  have hsucc (j : ℕ) : PowerSeries.coeff (j + 1) φ = exteriorForwardCoeff F j := by
    simp [φ, formalExteriorPhi, PowerSeries.coeff_succ_X_mul, exteriorFormalForward_coeff]
  have h1 : PowerSeries.coeff 1 φ = 0 := by
    simpa only [Nat.zero_add, exteriorForwardCoeff_zero] using hsucc 0
  have h2 : PowerSeries.coeff 2 φ = exteriorForwardCoeff F 1 := hsucc 1
  have h3 : PowerSeries.coeff 3 φ = exteriorForwardCoeff F 2 := hsucc 2
  change PowerSeries.coeff 0 (φ ^ 2) = 1 ∧
    PowerSeries.coeff 1 (φ ^ 2) = 0 ∧
    PowerSeries.coeff 2 (φ ^ 2) = 2 * exteriorForwardCoeff F 1 ∧
    PowerSeries.coeff 3 (φ ^ 2) = 2 * exteriorForwardCoeff F 2
  norm_num [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    h0, h1, h2, h3, two_mul]

theorem fourthMoment_finite_energy_eq (F : ℂ → ℂ) :
    (∑ d ∈ Finset.range 4, (2 - (d : ℝ) / 2) *
      ‖PowerSeries.coeff d (formalExteriorPhi (exteriorFormalForward F) ^ 2)‖ ^ 2) =
      2 + 4 * ‖exteriorForwardCoeff F 1‖ ^ 2 + 2 * ‖exteriorForwardCoeff F 2‖ ^ 2 := by
  obtain ⟨h0, h1, h2, h3⟩ := formalPhi_square_first_coefficients F
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, norm_mul]
  <;> ring

theorem rescaleExterior_boundary_four_le_coeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Real.circleAverage (fun ζ : ℂ => ‖rescaleExterior s F ζ‖ ^ 4) 0 1 ≤
      2 + 4 * ‖exteriorForwardCoeff (rescaleExterior s F) 1‖ ^ 2 +
        2 * ‖exteriorForwardCoeff (rescaleExterior s F) 2‖ ^ 2 := by
  have hh := rescaleExterior_even_boundary_moment_le_finite_energy F hc hs0 hs1 2
    (by norm_num)
  norm_num only [Nat.cast_ofNat, Nat.reduceMul] at hh
  rwa [fourthMoment_finite_energy_eq] at hh

end SpringerLean

#print axioms SpringerLean.rescaleExterior_boundary_four_le_coeff
