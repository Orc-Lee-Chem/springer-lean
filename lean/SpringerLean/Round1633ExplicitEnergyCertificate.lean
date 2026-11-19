import SpringerLean.Round1632ExplicitEnergyProfile

namespace SpringerLean

/-- The original 43-case homogeneous multiplier certificate now applies
to the explicit continuous spline at every nonnegative time. The
existential slopes permit either printed side at a knot. -/
theorem energyMultiplierSpline_allK_homogeneous
    {k : ℕ} (hk : 751 ≤ k) {t p w : ℝ}
    (ht : 0 ≤ t) (hp : 0 ≤ p) (hw : 0 ≤ w) :
    ∃ cp fp sp : ℝ,
      let v := energyMultiplierSplineValue t
      let A := energyMultiplierA (1/(k:ℝ)) fp sp v
      let B := energyMultiplierB (1/(k:ℝ)) (1/((k:ℝ)-1))
        ((k:ℝ)/(4*((k:ℝ)-1))) cp fp sp v
      let D := energyMultiplierD (1/((k:ℝ)-1)) (k:ℝ) cp v
      D*p^2+B*w*p+(1-A)*w^2 ≤ (25/16)*p^2 := by
  obtain ⟨cp,fp,sp,hprofile⟩ :=
    energyMultiplierSpline_profile_exists t ht
  refine ⟨cp,fp,sp,?_⟩
  exact energyMultiplier_allK_allTime_homogeneous
    hk ht hprofile hp hw

end SpringerLean

#print axioms SpringerLean.energyMultiplierSpline_allK_homogeneous
