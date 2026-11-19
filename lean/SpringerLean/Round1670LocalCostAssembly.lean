import SpringerLean.Round1662EnergyLocalCostLedger

namespace SpringerLean

/-- Once the seven geometric and phase costs have been bounded, their
sum is exactly the flux-cost expression used by the A/B/D ledger. -/
theorem energyFlux_local_cost_assembly
    (K : ℝ)
    (v : EnergyMultiplierValue) (cp fp sp p u w
      drift Ur yr geom ugrad sigmaGrad trace : ℝ)
    (hu : u^2 = w^2)
    (hDrift : K*(v.chi-v.sigma)*drift ≤
      K*|v.chi-v.sigma| * w*p)
    (hRadial : K*(2*v.f-(K/(4*(K-1)))*cp)*u*Ur ≤
      K*|2*v.f-(K/(4*(K-1)))*cp| * w*p)
    (hYr : -K*(v.f+v.t*fp)*yr*u^2 ≤
      2*K*|v.f+v.t*fp| * w^2+
      |v.f+v.t*fp| * w*p)
    (hGeom : K*geom*v.f*u^2 ≤
      2*K*(max 0 v.f)*w^2)
    (hChi : -(K/(4*(K-1)))*cp*v.t*ugrad ≤
      2*(K/(4*(K-1)))*v.t*|cp| * w*p+
      ((K/(4*(K-1)))/K)*v.t*|cp| * p^2)
    (hSigma : -(K/2)*sigmaGrad ≤
      (K^2/2)*|sp| * w^2+K*v.t*|sp| * w^2+
      (v.t*|sp|/2)*w*p)
    (hTrace : K*v.sigma*trace ≤
      K*v.sigma*w^2+v.sigma*w*p) :
    (K/(4*(K-1)))*v.chi*p^2-
      K^2*(v.chi+fp)*u^2+
      K*(v.chi-v.sigma)*drift+
      K*(2*v.f-(K/(4*(K-1)))*cp)*u*Ur-
      K*(v.f+v.t*fp)*yr*u^2+
      K*geom*v.f*u^2-
      (K/(4*(K-1)))*cp*v.t*ugrad-
      (K/2)*sigmaGrad+
      K*v.sigma*trace ≤
        energyMultiplierFluxCostBound K v cp fp sp p w := by
  dsimp [energyMultiplierFluxCostBound]
  rw [hu]
  rw [hu] at hYr hGeom
  nlinarith [hDrift,hRadial,hYr,hGeom,hChi,hSigma,hTrace]

end SpringerLean

#print axioms SpringerLean.energyFlux_local_cost_assembly
