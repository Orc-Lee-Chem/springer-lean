import SpringerLean.Round1708ActualKnotSignedFluxAE
import SpringerLean.Round1674ActualFluxCost

open scoped ComplexConjugate
open MeasureTheory

namespace SpringerLean
noncomputable section

/-- The same A/B/D local cost bound as on an open multiplier cell now
holds almost everywhere at every physical knot, for arbitrary
one-sided slope data. -/
theorem actualEnergyFlux_cost_le_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        ∀ cp fp sp : ℝ,
          let U := actualHarmonicPhaseField F k beta
          let t := actualHarmonicMultiplierTime F k z
          let v := energyMultiplierSplineValue t
          let p := Real.sqrt
            (((fderiv ℝ U z) (1 : ℂ))^2 +
             ((fderiv ℝ U z) Complex.I)^2)
          let u := U z / ‖actualHarmonic F z‖
          let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
          b * actualEnergyFluxDiv F k beta z ≤
            energyMultiplierFluxCostBound (k : ℝ) v cp fp sp p |u| := by
  filter_upwards
    [actualEnergyFlux_signed_ledger_knot_ae F hc k hk beta,
      actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k]
    with z hledger hcomp i hreg hlevel cp fp sp
  obtain ⟨hz, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k z
  let v := energyMultiplierSplineValue t
  let ux := (fderiv ℝ U z) (1 : ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2 + uy^2)
  let u := U z / y z
  let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
  let Q := (conj (actualHarmonic F z))⁻¹
  let Ur := (fderiv ℝ U z) (z / ‖z‖)
  let yr := (fderiv ℝ y z) (z / ‖z‖)
  let drift := U z * (Q.re * ux + Q.im * uy)
  let ugrad := u * ((fderiv ℝ y z) (1 : ℂ) * ux +
    (fderiv ℝ y z) Complex.I * uy)
  let sigmaGrad := (U z)^2 *
    ((fderiv ℝ (fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w)) z) (1 : ℂ) * Q.re +
     (fderiv ℝ (fun w => energyMultiplierSigma
      (actualHarmonicMultiplierTime F k w)) z) Complex.I * Q.im)
  let ctrace := (U z)^2 *
    (deriv (exteriorForwardGerm F) (conj z) /
      (actualHarmonic F z)^2).re
  have hK : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hK0 : (k : ℝ) ≠ 0 := ne_of_gt hK
  have hu : u^2 = |u|^2 := (sq_abs u).symm
  have hSigned := hledger i hreg hlevel cp fp
  have hDrift := actualHarmonicPhase_drift_cross_cost_le
    F k beta z (v.chi - v.sigma)
  have hRadial := actualHarmonicPhase_radial_cross_cost_le
    F k beta hz0 (2 * v.f - b * cp)
  have hYr := actualHarmonicPhase_radial_modulus_cost_le
    F hc k (by omega) beta hbeta hz hz0 hH (v.f + v.t * fp)
  have hGeom0 := actualHarmonic_radial_multiplier_positivePart_le
    F hc hz hz0 v.f
  have hGeom : (k : ℝ) * (y z / ‖z‖) * v.f * u^2 ≤
      2 * (k : ℝ) * (max 0 v.f) * |u|^2 := by
    have hfac : 0 ≤ (k : ℝ) * u^2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hGeom0 hfac
    calc
      (k : ℝ) * (y z / ‖z‖) * v.f * u^2 =
        (k : ℝ) * u^2 * ((y z / ‖z‖) * v.f) := by ring
      _ ≤ (k : ℝ) * u^2 * (2 * max 0 v.f) := hh
      _ = 2 * (k : ℝ) * (max 0 v.f) * |u|^2 := by rw [← hu]; ring
  have hChi := actualHarmonicPhase_chi_gradient_cost_le
    F hc k hk beta hbeta hz hH cp
  have hTrace0 := actualHarmonicPhase_sigma_trace_cost_le
    F hc k (by omega) beta hbeta hz hH
  have hTrace0' : v.sigma * ctrace ≤
      v.sigma * (u^2 + |u| * p / (k : ℝ)) := by
    simpa only [v, energyMultiplierSplineValue, ctrace, u, y, p, t,
      mul_assoc] using hTrace0
  have hTrace : (k : ℝ) * v.sigma * ctrace ≤
      (k : ℝ) * v.sigma * |u|^2 + v.sigma * |u| * p := by
    have hh := mul_le_mul_of_nonneg_left hTrace0' (le_of_lt hK)
    calc
      (k : ℝ) * v.sigma * ctrace =
        (k : ℝ) * (v.sigma * ctrace) := by ring
      _ ≤ (k : ℝ) * (v.sigma * (u^2 + |u| * p / (k : ℝ))) := hh
      _ = (k : ℝ) * v.sigma * |u|^2 + v.sigma * |u| * p := by
        rw [← hu]
        field_simp [hK0]
  have hYr' : -(k : ℝ) * (v.f + v.t * fp) * yr * u^2 ≤
      2 * (k : ℝ) * |v.f + v.t * fp| * |u|^2 +
      |v.f + v.t * fp| * |u| * p := by
    calc
      _ ≤ 2 * (k : ℝ) * |v.f + v.t * fp| * u^2 +
          |v.f + v.t * fp| * |u| * p := hYr
      _ = _ := by rw [hu]
  have hChi' : -b * cp * v.t * ugrad ≤
      2 * b * v.t * |cp| * |u| * p +
      (b / (k : ℝ)) * v.t * |cp| * p^2 := by
    simpa only [v, energyMultiplierSplineValue, ugrad,
      mul_assoc] using hChi
  have hSigmaZero : sigmaGrad = 0 := by
    have hsigma := (hcomp i hreg hlevel).2.2.fderiv
    simp [sigmaGrad, hsigma]
  have hSigma' : -((k : ℝ) / 2) * sigmaGrad ≤
      ((k : ℝ)^2 / 2) * |sp| * |u|^2 +
      (k : ℝ) * v.t * |sp| * |u|^2 +
      (v.t * |sp| / 2) * |u| * p := by
    rw [hSigmaZero]
    simp only [mul_zero, neg_zero]
    have ht : 0 ≤ t := actualHarmonicMultiplierTime_nonneg F k hz
    change 0 ≤ ((k : ℝ)^2 / 2) * |sp| * |u|^2 +
      (k : ℝ) * t * |sp| * |u|^2 +
      (t * |sp| / 2) * |u| * p
    positivity
  have hAssembly := energyFlux_local_cost_assembly
    (K := (k : ℝ)) (v := v) (cp := cp) (fp := fp)
    (sp := sp) (p := p) (u := u) (w := |u|)
    (drift := drift) (Ur := Ur) (yr := yr)
    (geom := y z / ‖z‖) (ugrad := ugrad)
    (sigmaGrad := sigmaGrad) (trace := ctrace)
    hu hDrift hRadial hYr' hGeom hChi' hSigma' hTrace
  dsimp only at hSigned hAssembly ⊢
  have hp2 : ux^2 + uy^2 = p^2 := by
    rw [Real.sq_sqrt (by positivity : 0 ≤ ux^2 + uy^2)]
  rw [hp2] at hSigned
  rw [hSigned]
  convert hAssembly using 1 <;>
    (simp only [v, energyMultiplierSplineValue, y, u, t, p, b,
      Q, Ur, yr, drift, ugrad, sigmaGrad, ctrace]; ring)

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_cost_le_knot_ae
