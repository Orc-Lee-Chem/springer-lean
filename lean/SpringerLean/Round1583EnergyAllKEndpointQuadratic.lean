import SpringerLean.Round1582EnergyRealBaselineBridge

namespace SpringerLean
set_option maxHeartbeats 1000000

/-- The endpoint quadratic is monotone in the three coefficients in
the direction supplied by the uniform-k envelope, for s>=0. -/
theorem signedEnergyQuadratic_le_of_coefficient_envelope
    {A₀ D₀ B₀ A D B C s : ℝ}
    (hA : A₀ ≤ A) (hD : D ≤ D₀) (hB : B ≤ B₀) (hs : 0 ≤ s)
    (hbase : signedEnergyQuadratic A₀ B₀ D₀ s ≤ C) :
    signedEnergyQuadratic A B D s ≤ C := by
  have hBterm := mul_nonneg (sub_nonneg.mpr hB) hs
  have hAterm := mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg s)
  dsimp [signedEnergyQuadratic] at *
  nlinarith

/-- The 43 exact endpoint certificates imply the energy quadratic
bound at every k>=751, at each one-sided endpoint, for s>=0.
Interpolation between endpoints and the analytic multiplier integration
are separate requirements. -/
theorem energyMultiplier_allK_endpoint_quadratic
    {k : ℕ} (hk : 751 ≤ k) (j : Fin 43)
    {s : ℝ} (hs : 0 ≤ s) :
    let v := energyMultiplierEndpointRaw j
    let chi : ℝ := v.chi
    let f : ℝ := v.f
    let sigma : ℝ := v.sigma
    let cp : ℝ := v.cp
    let fp : ℝ := v.fp
    let sp : ℝ := v.sp
    let t : ℝ := v.t
    let h := f+t*fp
    let Q := 2*max (0:ℝ) f+2*|h|+t*|sp|+sigma
    let P := |h|+t*|sp|/2+sigma
    signedEnergyQuadratic
      (chi+fp-|sp|/2-Q/(k:ℝ))
      (|chi-sigma|+|2*f-((k:ℝ)/(4*((k:ℝ)-1)))*cp|+
        t*|cp|/(2*((k:ℝ)-1))+P/(k:ℝ))
      (((k:ℝ)*chi+t*|cp|)/(4*((k:ℝ)-1))) s ≤ 25/16 := by
  dsimp only
  have henv := energyMultiplier_all43_k_envelope hk j
  have heq := energyMultiplier_all43_real_baseline_eq j
  rcases hcoeff : energyMultiplierEndpointCoeffs j with ⟨A₀,D₀,B₀⟩
  simp only [hcoeff] at heq
  change (A₀:ℝ) = _ ∧ (D₀:ℝ) = _ ∧ (B₀:ℝ) = _ at heq
  obtain ⟨heqA,heqD,heqB⟩ := heq
  obtain ⟨hA,hD,hB⟩ := henv
  rw [←heqA] at hA
  rw [←heqD] at hD
  rw [←heqB] at hB
  have hbase := energyMultiplierEndpoint_quadratic_all43 j s
  simp only [hcoeff] at hbase
  exact signedEnergyQuadratic_le_of_coefficient_envelope
    hA hD hB hs hbase

end SpringerLean

#print axioms SpringerLean.signedEnergyQuadratic_le_of_coefficient_envelope
#print axioms SpringerLean.energyMultiplier_allK_endpoint_quadratic
