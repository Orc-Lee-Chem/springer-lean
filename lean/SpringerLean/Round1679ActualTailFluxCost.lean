import SpringerLean.Round1678ActualTailSignedFlux
import SpringerLean.Round1674ActualFluxCost

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- Actual combined flux cost on the constant multiplier tail. -/
theorem actualEnergyFlux_cost_le_tail
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (htail : 1 < actualHarmonicMultiplierTime F k z) :
    let U := actualHarmonicPhaseField F k beta
    let t := actualHarmonicMultiplierTime F k z
    let v := energyMultiplierSplineValue t
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    let u := U z/‖actualHarmonic F z‖
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    b*actualEnergyFluxDiv F k beta z ≤
      energyMultiplierFluxCostBound (k:ℝ) v 0 0 0 p |u| := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k z
  let v := energyMultiplierSplineValue t
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let u := U z/y z
  let b := (k:ℝ)/(4*((k:ℝ)-1))
  let Q := (conj (actualHarmonic F z))⁻¹
  let Ur := (fderiv ℝ U z) (z/‖z‖)
  let yr := (fderiv ℝ y z) (z/‖z‖)
  let drift := U z*(Q.re*ux+Q.im*uy)
  let ctrace := (U z)^2 *
    (deriv (exteriorForwardGerm F) (conj z) /
      (actualHarmonic F z)^2).re
  have hK : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hK0 : (k:ℝ) ≠ 0 := ne_of_gt hK
  have hu : u^2 = |u|^2 := (sq_abs u).symm
  have hSigned := actualEnergyFlux_signed_ledger_tail
    F hc k hk beta hz hz0 hH htail
  have hDrift := actualHarmonicPhase_drift_cross_cost_le
    F k beta z (v.chi-v.sigma)
  have hRadial := actualHarmonicPhase_radial_cross_cost_le
    F k beta hz0 (2*v.f)
  have hRadial' : (k:ℝ)*(2*v.f-b*0)*u*Ur ≤
      (k:ℝ)*|2*v.f-b*0| * |u| * p := by
    simpa only [mul_zero, sub_zero] using hRadial
  have hYr := actualHarmonicPhase_radial_modulus_cost_le
    F hc k (by omega) beta hbeta hz hz0 hH v.f
  have hYr' : -(k:ℝ)*v.f*yr*u^2 ≤
      2*(k:ℝ)*|v.f| * |u|^2+|v.f| * |u| * p := by
    calc
      _ ≤ 2*(k:ℝ)*|v.f| * u^2+|v.f| * |u| * p := hYr
      _ = _ := by rw [hu]
  have hYr'' : -(k:ℝ)*(v.f+v.t*0)*yr*u^2 ≤
      2*(k:ℝ)*|v.f+v.t*0| * |u|^2+
      |v.f+v.t*0| * |u| * p := by
    simpa only [mul_zero, add_zero] using hYr'
  have hGeom0 := actualHarmonic_radial_multiplier_positivePart_le
    F hc hz hz0 v.f
  have hGeom : (k:ℝ)*(y z/‖z‖)*v.f*u^2 ≤
      2*(k:ℝ)*(max 0 v.f)*|u|^2 := by
    have hfac : 0 ≤ (k:ℝ)*u^2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hGeom0 hfac
    calc
      (k:ℝ)*(y z/‖z‖)*v.f*u^2 =
        (k:ℝ)*u^2*((y z/‖z‖)*v.f) := by ring
      _ ≤ (k:ℝ)*u^2*(2*max 0 v.f) := hh
      _ = 2*(k:ℝ)*(max 0 v.f)*|u|^2 := by rw [← hu]; ring
  have hTrace0 := actualHarmonicPhase_sigma_trace_cost_le
    F hc k (by omega) beta hbeta hz hH
  have hTrace0' : v.sigma*ctrace ≤
      v.sigma*(u^2+|u| * p/(k:ℝ)) := by
    simpa only [v, energyMultiplierSplineValue, ctrace, u, y, p, t,
      mul_assoc] using hTrace0
  have hTrace : (k:ℝ)*v.sigma*ctrace ≤
      (k:ℝ)*v.sigma * |u|^2+v.sigma * |u| * p := by
    have hh := mul_le_mul_of_nonneg_left hTrace0' (le_of_lt hK)
    calc
      (k:ℝ)*v.sigma*ctrace = (k:ℝ)*(v.sigma*ctrace) := by ring
      _ ≤ (k:ℝ)*(v.sigma*(u^2+|u| * p/(k:ℝ))) := hh
      _ = (k:ℝ)*v.sigma * |u|^2+v.sigma * |u| * p := by
        rw [← hu]
        field_simp [hK0]
  have hChi : -b*(0:ℝ)*v.t*(0:ℝ) ≤
      2*b*v.t*|((0:ℝ))| * |u| * p+
      (b/(k:ℝ))*v.t*|((0:ℝ))| * p^2 := by simp
  have hSigma : -((k:ℝ)/2)*(0:ℝ) ≤
      ((k:ℝ)^2/2)*|((0:ℝ))| * |u|^2+
      (k:ℝ)*v.t*|((0:ℝ))| * |u|^2+
      (v.t*|((0:ℝ))|/2)*|u| * p := by simp
  have hAssembly := energyFlux_local_cost_assembly
    (K := (k:ℝ)) (v := v) (cp := 0) (fp := 0)
    (sp := 0) (p := p) (u := u) (w := |u|)
    (drift := drift) (Ur := Ur) (yr := yr)
    (geom := y z/‖z‖) (ugrad := 0)
    (sigmaGrad := 0) (trace := ctrace)
    hu hDrift hRadial' hYr'' hGeom hChi hSigma hTrace
  dsimp only at hSigned hAssembly ⊢
  have hp2 : ux^2+uy^2 = p^2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ ux^2+uy^2)]
  rw [hp2] at hSigned
  rw [hSigned]
  convert hAssembly using 1 <;>
    (simp only [v, energyMultiplierSplineValue, y, u, t, p, b,
      Q, Ur, yr, drift, ctrace]; ring)

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_cost_le_tail
