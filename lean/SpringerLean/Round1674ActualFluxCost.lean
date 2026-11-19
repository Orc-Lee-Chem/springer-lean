import SpringerLean.Round1669ActualSignedFluxLedger
import SpringerLean.Round1670LocalCostAssembly
import SpringerLean.Round1671ActualMixedCrossCosts
import SpringerLean.Round1672ActualRadialModulusCost
import SpringerLean.Round1673ActualChiGradientCost
import SpringerLean.Round1661ActualRadialPositivePart

open scoped ComplexConjugate

namespace SpringerLean
noncomputable section

/-- The exact local A/B/D flux cost for the actual centered exterior
map, on every open affine multiplier cell. -/
theorem actualEnergyFlux_cost_le_cell
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k z
    let v := energyMultiplierSplineValue t
    let cp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).cp
    let fp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).fp
    let sp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).sp
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    let u := U z/y z
    let b := (k:ℝ)/(4*((k:ℝ)-1))
    b*actualEnergyFluxDiv F k beta z ≤
      energyMultiplierFluxCostBound (k:ℝ) v cp fp sp p |u| := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k z
  let v := energyMultiplierSplineValue t
  let cp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).cp
  let fp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).fp
  let sp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).sp
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let u := U z/y z
  let b := (k:ℝ)/(4*((k:ℝ)-1))
  let Q := (conj (actualHarmonic F z))⁻¹
  let Ur := (fderiv ℝ U z) (z/‖z‖)
  let yr := (fderiv ℝ y z) (z/‖z‖)
  let drift := U z*(Q.re*ux+Q.im*uy)
  let ugrad := u*((fderiv ℝ y z) (1:ℂ)*ux+
    (fderiv ℝ y z) Complex.I*uy)
  let sigmaGrad := (U z)^2 *
    ((fderiv ℝ (fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w)) z) (1:ℂ)*Q.re+
     (fderiv ℝ (fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w)) z) Complex.I*Q.im)
  let ctrace := (U z)^2 *
    (deriv (exteriorForwardGerm F) (conj z) /
      (actualHarmonic F z)^2).re
  have hK : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hK0 : (k:ℝ) ≠ 0 := ne_of_gt hK
  have hu : u^2 = |u|^2 := (sq_abs u).symm
  have hSigned := actualEnergyFlux_signed_ledger_cell
    F hc k hk beta i hz hz0 hH hleft hright
  have hDrift := actualHarmonicPhase_drift_cross_cost_le
    F k beta z (v.chi-v.sigma)
  have hRadial := actualHarmonicPhase_radial_cross_cost_le
    F k beta hz0 (2*v.f-b*cp)
  have hYr := actualHarmonicPhase_radial_modulus_cost_le
    F hc k (by omega) beta hbeta hz hz0 hH (v.f+v.t*fp)
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
  have hChi := actualHarmonicPhase_chi_gradient_cost_le
    F hc k hk beta hbeta hz hH cp
  have hSigma := actualHarmonicPhase_sigma_gradient_cost_le
    F hc k (by omega) beta hbeta i hz hz0 hH hleft hright
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
      (k:ℝ)*v.sigma*ctrace =
        (k:ℝ)*(v.sigma*ctrace) := by ring
      _ ≤ (k:ℝ)*(v.sigma*(u^2+|u| * p/(k:ℝ))) := hh
      _ = (k:ℝ)*v.sigma * |u|^2+v.sigma * |u| * p := by
        rw [← hu]
        field_simp [hK0]
  have hYr' : -(k:ℝ)*(v.f+v.t*fp)*yr*u^2 ≤
      2*(k:ℝ)*|v.f+v.t*fp| * |u|^2+
      |v.f+v.t*fp| * |u| * p := by
    calc
      _ ≤ 2*(k:ℝ)*|v.f+v.t*fp| * u^2+
          |v.f+v.t*fp| * |u| * p := hYr
      _ = _ := by rw [hu]
  have hChi' : -b*cp*v.t*ugrad ≤
      2*b*v.t*|cp| * |u| * p+(b/(k:ℝ))*v.t*|cp| * p^2 := by
    simpa only [v, energyMultiplierSplineValue, ugrad,
      mul_assoc] using hChi
  have hSigma' : -((k:ℝ)/2)*sigmaGrad ≤
      ((k:ℝ)^2/2)*|sp| * |u|^2+
      (k:ℝ)*v.t*|sp| * |u|^2+
      (v.t*|sp|/2)*|u| * p := by
    have hs : -(k:ℝ)/2*sigmaGrad ≤
        ((k:ℝ)^2/2)*|sp| * u^2+
        (k:ℝ)*v.t*|sp| * u^2+
        (v.t*|sp|/2)*|u| * p := by
      simpa only [sigmaGrad, v, energyMultiplierSplineValue,
        u, y, t, sp, Q, U, ux, uy, p, mul_assoc] using hSigma
    calc
      -((k:ℝ)/2)*sigmaGrad = -(k:ℝ)/2*sigmaGrad := by ring
      _ ≤ ((k:ℝ)^2/2)*|sp| * u^2+
          (k:ℝ)*v.t*|sp| * u^2+
          (v.t*|sp|/2)*|u| * p := hs
      _ = _ := by rw [hu]
  have hAssembly := energyFlux_local_cost_assembly
    (K := (k:ℝ)) (v := v) (cp := cp) (fp := fp)
    (sp := sp) (p := p) (u := u) (w := |u|)
    (drift := drift) (Ur := Ur) (yr := yr)
    (geom := y z/‖z‖) (ugrad := ugrad)
    (sigmaGrad := sigmaGrad) (trace := ctrace)
    hu hDrift hRadial hYr' hGeom hChi' hSigma' hTrace
  dsimp only at hSigned hAssembly ⊢
  have hp2 : ux^2+uy^2 = p^2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ ux^2+uy^2)]
  rw [hp2] at hSigned
  rw [hSigned]
  convert hAssembly using 1 <;>
    (simp only [v, energyMultiplierSplineValue, y, u, t, p, b,
      Q, Ur, yr, drift, ugrad, sigmaGrad, ctrace]; ring)

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_cost_le_cell
