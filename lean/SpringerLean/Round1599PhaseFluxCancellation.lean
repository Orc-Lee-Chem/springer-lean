import SpringerLean.Round1598AllTimeHomogeneousMultiplier

namespace SpringerLean

/-- The exact drift and radial cancellations in the proposed combined
flux. They must be performed before taking absolute values. -/
theorem phaseFlux_combined_cancellation
    {k chi sigma f cp drift radial : ℝ} (hk : k ≠ 1) :
    let b := k/(4*(k-1))
    b*(4*(k-1)*chi*drift - 4*(k-1)*sigma*drift +
       4*(k-1)*2*f*radial - k*cp*radial) =
      k*(chi-sigma)*drift + k*(2*f-b*cp)*radial := by
  dsimp only
  field_simp [sub_ne_zero.mpr hk]
  ring

/-- The all-time homogeneous certificate turns the one remaining
pointwise flux estimate into the paper's C=25/16 pointwise inequality.
The premise is precisely the divergence inequality still to be proved
for the actual three fluxes. -/
theorem phaseEnergy_pointwise_of_flux_bound
    {k : ℕ} (hk : 751 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    {v : EnergyMultiplierValue} {cp fp sp p u b fluxDiv : ℝ}
    (hprofile : EnergyMultiplierProfileAt t v cp fp sp)
    (hp : 0 ≤ p)
    (hflux :
      let A := energyMultiplierA (1/(k:ℝ)) fp sp v
      let B := energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) cp fp sp v
      let D := energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) cp v
      (k:ℝ)^2*A*u^2+b*fluxDiv ≤ D*p^2+(k:ℝ)*B * |u| * p) :
    (k:ℝ)^2*u^2+b*fluxDiv ≤ (25/16)*p^2 := by
  have hv : 0 ≤ (k:ℝ)*|u| := by positivity
  have hhom := energyMultiplier_allK_allTime_homogeneous
    hk ht hprofile hp hv (w := (k:ℝ)*|u|)
  dsimp only at hhom hflux
  have hu : ((k:ℝ)*|u|)^2 = (k:ℝ)^2*u^2 := by
    rw [mul_pow, sq_abs]
  rw [hu] at hhom
  nlinarith [hhom, hflux]

end SpringerLean

#print axioms SpringerLean.phaseFlux_combined_cancellation
#print axioms SpringerLean.phaseEnergy_pointwise_of_flux_bound
