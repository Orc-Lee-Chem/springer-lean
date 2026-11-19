import SpringerLean.Round1575EnergyEndpointData
import SpringerLean.Round1486EnergyQuadraticReduction

namespace SpringerLean
set_option maxHeartbeats 640000

/-- Transport a rational completed-square certificate to the real
quadratic form used in the analytic energy estimate. -/
theorem rational_energy_quadratic_le
    {A D B : ℚ}
    (hA : 1 < A) (hD : D ≤ 25/16)
    (hdisc : B^2 ≤ 4*(A-1)*(25/16-D)) (s : ℝ) :
    signedEnergyQuadratic (A:ℝ) (B:ℝ) (D:ℝ) s ≤ 25/16 := by
  apply signedEnergyQuadratic_le_of_discriminant
  · exact_mod_cast hA
  · have h : (D:ℝ) ≤ ((25/16:ℚ):ℝ) := by exact_mod_cast hD
    convert h using 1 <;> norm_num
  · have h : ((B^2:ℚ):ℝ) ≤
        ((4*(A-1)*(25/16-D):ℚ):ℝ) := by exact_mod_cast hdisc
    convert h using 1 <;> push_cast <;> norm_num <;> ring

/-- All 43 one-sided multiplier endpoint quadratics obey the same
real bound `25/16` for every slope ratio. This is the finite arithmetic
input, before the analytic PDE and interpolation are applied. -/
theorem energyMultiplierEndpoint_quadratic_all43
    (j : Fin 43) (s : ℝ) :
    let (A,D,B) := energyMultiplierEndpointCoeffs j
    signedEnergyQuadratic (A:ℝ) (B:ℝ) (D:ℝ) s ≤ 25/16 := by
  dsimp only
  rcases hcoeff : energyMultiplierEndpointCoeffs j with ⟨A,D,B⟩
  have hvalid := energyMultiplierEndpoint_all43 j
  simp only [energyMultiplierEndpointValid,hcoeff] at hvalid
  change 1 < A ∧ D ≤ (25/16:ℚ) ∧
    B^2 ≤ 4*(A-1)*((25/16:ℚ)-D) at hvalid
  exact rational_energy_quadratic_le hvalid.1 hvalid.2.1 hvalid.2.2 s

end SpringerLean

#print axioms SpringerLean.rational_energy_quadratic_le
#print axioms SpringerLean.energyMultiplierEndpoint_quadratic_all43
