import SpringerLean.Round1585EnergySegmentConvex

namespace SpringerLean
noncomputable section

/-- The sum of the separate upper costs of the actual three-flux
divergence after the signed drift and radial terms have been combined.
The individual analytic estimates are proved separately. -/
def energyMultiplierFluxCostBound
    (K : ℝ) (v : EnergyMultiplierValue) (cp fp sp p u : ℝ) : ℝ :=
  let b := K/(4*(K-1))
  let h := v.f+v.t*fp
  b*v.chi*p^2-K^2*(v.chi+fp)*u^2+
    K * |v.chi-v.sigma| * u*p+
    K * |2*v.f-b*cp| * u*p+
    2*K * |h| * u^2+|h| * u*p+
    2*K*(max 0 v.f)*u^2+
    2*b*v.t*|cp| * u*p+(b/K)*v.t*|cp| * p^2+
    (K^2/2)*|sp| * u^2+K*v.t*|sp| * u^2+
    (v.t*|sp|/2)*u*p+
    K*v.sigma*u^2+v.sigma*u*p

/-- Exact accounting identity: the original A/B/D coefficients pay
precisely the local divergence costs, without spare or missing terms. -/
theorem energyMultiplier_local_cost_ledger
    (K : ℝ) (hK : 1 < K)
    (v : EnergyMultiplierValue) (cp fp sp p u : ℝ) :
    K^2*(energyMultiplierA (1/K) fp sp v)*u^2+
      energyMultiplierFluxCostBound K v cp fp sp p u =
    (energyMultiplierD (1/(K-1)) K cp v)*p^2+
      K*(energyMultiplierB (1/K) (1/(K-1))
        (K/(4*(K-1))) cp fp sp v)*u*p := by
  have hK0 : K ≠ 0 := by linarith
  have hKm1 : K-1 ≠ 0 := by linarith
  dsimp [energyMultiplierFluxCostBound, energyMultiplierA,
    energyMultiplierB, energyMultiplierD, coeffQ, coeffP]
  field_simp [hK0, hKm1]
  ring

end
end SpringerLean

#print axioms SpringerLean.energyMultiplier_local_cost_ledger
