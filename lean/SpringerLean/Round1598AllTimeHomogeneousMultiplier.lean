import SpringerLean.Round1597HomogeneousAllSlope

namespace SpringerLean

/-- The complete all-time multiplier certificate in the homogeneous
form used by the pointwise phase-field estimate. It includes p=0 and
all valid one-sided slopes at every knot. -/
theorem energyMultiplier_allK_allTime_homogeneous
    {k : ℕ} (hk : 751 ≤ k) {t : ℝ} (ht : 0 ≤ t)
    {v : EnergyMultiplierValue} {cp fp sp p w : ℝ}
    (hprofile : EnergyMultiplierProfileAt t v cp fp sp)
    (hp : 0 ≤ p) (hw : 0 ≤ w) :
    let A := energyMultiplierA (1/(k:ℝ)) fp sp v
    let B := energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
      ((k:ℝ)/(4*((k:ℝ)-1))) cp fp sp v
    let D := energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) cp v
    D*p^2+B*w*p+(1-A)*w^2 ≤ (25/16)*p^2 := by
  dsimp only
  apply signedEnergyQuadratic_homogeneous_of_all_s hp hw
  intro s hs
  exact energyMultiplier_allK_allTime_quadratic hk ht hprofile hs

end SpringerLean

#print axioms SpringerLean.energyMultiplier_allK_allTime_homogeneous
