import SpringerLean.Round1629EnergyCellInterpolationData

namespace SpringerLean

/-- The actual global multiplier value triple at one time. -/
def energyMultiplierSplineValue (t : ℝ) : EnergyMultiplierValue :=
  ⟨t, energyMultiplierChi t, energyMultiplierF t,
    energyMultiplierSigma t⟩

theorem EnergyMultiplierValue.ext {v w : EnergyMultiplierValue}
    (ht : v.t = w.t) (hchi : v.chi = w.chi)
    (hf : v.f = w.f) (hsigma : v.sigma = w.sigma) : v = w := by
  cases v
  cases w
  simp_all

/-- The global spline is exactly the cell value used by the 43-case
energy certificate, including both endpoints. -/
theorem energyMultiplierSplineValue_eq_cell
    (i : Fin 21) (lam t : ℝ)
    (ht : (energyMultiplierCellValue i lam).t = t)
    (hleft : energyMultiplierKnotTime i.castSucc ≤ t)
    (hright : t ≤ energyMultiplierKnotTime i.succ) :
    energyMultiplierSplineValue t = energyMultiplierCellValue i lam := by
  let r₀ := energyMultiplierEndpointRaw (2*i.val)
  let r₁ := energyMultiplierEndpointRaw (2*i.val+1)
  have htimes := energyMultiplier_cell_endpoint_times i
  change r₀.t = energyMultiplierKnotTime i.castSucc ∧
    r₁.t = energyMultiplierKnotTime i.succ at htimes
  have hinc := energyMultiplier_cell_endpoint_increments i
  have hinc' : (r₀.cp:ℝ)*((r₁.t:ℝ)-(r₀.t:ℝ)) =
      (r₁.chi:ℝ)-(r₀.chi:ℝ) ∧
    (r₀.fp:ℝ)*(r₁.t-r₀.t) = (r₁.f:ℝ)-(r₀.f:ℝ) ∧
    (r₀.sp:ℝ)*(r₁.t-r₀.t) =
      (r₁.sigma:ℝ)-(r₀.sigma:ℝ) := by
    simpa only [Rat.cast_sub] using hinc
  have hv := energyMultiplierSpline_on_cell i t hleft hright
  change energyMultiplierChi t = (r₀.chi:ℝ)+(r₀.cp:ℝ)*
      (t-energyMultiplierKnotTime i.castSucc) ∧
    energyMultiplierF t = (r₀.f:ℝ)+(r₀.fp:ℝ)*
      (t-energyMultiplierKnotTime i.castSucc) ∧
    energyMultiplierSigma t = (r₀.sigma:ℝ)+(r₀.sp:ℝ)*
      (t-energyMultiplierKnotTime i.castSucc) at hv
  have ht' : t = (1-lam)*r₀.t+lam*r₁.t := by
    simpa only [energyMultiplierCellValue,
      energyMultiplierValueRaw] using ht.symm
  have hstep : t-r₀.t = lam*(r₁.t-r₀.t) := by
    rw [ht']
    ring
  apply EnergyMultiplierValue.ext
  · exact ht.symm
  · change energyMultiplierChi t =
      (1-lam)*(r₀.chi:ℝ)+lam*(r₁.chi:ℝ)
    rw [hv.1, ← htimes.1, hstep]
    have hm := congrArg (fun x : ℝ => lam*x) hinc'.1
    nlinarith [hm]
  · change energyMultiplierF t =
      (1-lam)*(r₀.f:ℝ)+lam*(r₁.f:ℝ)
    rw [hv.2.1, ← htimes.1, hstep]
    have hm := congrArg (fun x : ℝ => lam*x) hinc'.2.1
    nlinarith [hm]
  · change energyMultiplierSigma t =
      (1-lam)*(r₀.sigma:ℝ)+lam*(r₁.sigma:ℝ)
    rw [hv.2.2, ← htimes.1, hstep]
    have hm := congrArg (fun x : ℝ => lam*x) hinc'.2.2
    nlinarith [hm]

end SpringerLean

#print axioms SpringerLean.energyMultiplierSplineValue_eq_cell
