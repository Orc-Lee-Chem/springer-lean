import SpringerLean.Round1707ActualKnotChiCancellationAE
import SpringerLean.Round1669ActualSignedFluxLedger

open scoped ComplexConjugate
open MeasureTheory

namespace SpringerLean
noncomputable section

/-- The signed three-flux ledger at every actual physical knot. The
one-sided slopes are arbitrary because the physical time is flat
almost everywhere on the knot level. -/
theorem actualEnergyFlux_signed_ledger_knot_ae
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℂ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      ∀ i : Fin 22,
        z ∈ actualMultiplierRegularSet F →
        actualHarmonicMultiplierTime F k z = energyMultiplierKnotTime i →
        ∀ cp fp : ℝ,
          let U := actualHarmonicPhaseField F k beta
          let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
          let t := actualHarmonicMultiplierTime F k
          let chi := energyMultiplierChi (t z)
          let f := energyMultiplierF (t z)
          let sigma := energyMultiplierSigma (t z)
          let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
          let Q := (conj (actualHarmonic F z))⁻¹
          let ux := (fderiv ℝ U z) (1 : ℂ)
          let uy := (fderiv ℝ U z) Complex.I
          let u := U z / y z
          let Ur := (fderiv ℝ U z) (z / ‖z‖)
          let yr := (fderiv ℝ y z) (z / ‖z‖)
          let drift := U z * (Q.re * ux + Q.im * uy)
          let ugrad := u *
            ((fderiv ℝ y z) (1 : ℂ) * ux +
              (fderiv ℝ y z) Complex.I * uy)
          let sigmaGrad := (U z)^2 *
            ((fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) (1 : ℂ) * Q.re +
              (fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) Complex.I * Q.im)
          let ctrace := (U z)^2 *
            (deriv (exteriorForwardGerm F) (conj z) /
              (actualHarmonic F z)^2).re
          b * actualEnergyFluxDiv F k beta z =
            b * chi * (ux^2 + uy^2) -
            (k : ℝ)^2 * (chi + fp) * u^2 +
            (k : ℝ) * (chi - sigma) * drift +
            (k : ℝ) * (2 * f - b * cp) * u * Ur -
            (k : ℝ) * (f + t z * fp) * yr * u^2 +
            (k : ℝ) * (y z / ‖z‖) * f * u^2 -
            b * cp * t z * ugrad -
            ((k : ℝ) / 2) * sigmaGrad +
            (k : ℝ) * sigma * ctrace := by
  filter_upwards
    [actualEnergyFluxPdiv_knot_ae F hc k beta,
      actualEnergyFluxRdiv_knot_anySlope_ae F hc k beta,
      actualEnergyFluxSdiv_knot_ae F hc k beta,
      actualEnergyMultiplier_chi_gradient_identity_knot_ae F hc k beta,
      actualHarmonicMultiplier_all_knot_hasFDerivAt_zero_ae F hc k]
    with z hP0 hR0 hS0 hchi0 hcomp i hreg hlevel cp fp
  obtain ⟨hz, hH, hz0⟩ :=
    (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  let chi := energyMultiplierChi (t z)
  let f := energyMultiplierF (t z)
  let sigma := energyMultiplierSigma (t z)
  let b := (k : ℝ) / (4 * ((k : ℝ) - 1))
  let Q := (conj (actualHarmonic F z))⁻¹
  let ux := (fderiv ℝ U z) (1 : ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let u := U z / y z
  let Ur := (fderiv ℝ U z) (z / ‖z‖)
  let yr := (fderiv ℝ y z) (z / ‖z‖)
  let drift := U z * (Q.re * ux + Q.im * uy)
  let ugrad := u * ((fderiv ℝ y z) (1 : ℂ) * ux +
    (fderiv ℝ y z) Complex.I * uy)
  let sigmaGrad := (U z)^2 *
    ((fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) (1 : ℂ) * Q.re +
      (fderiv ℝ (fun w => energyMultiplierSigma (t w)) z) Complex.I * Q.im)
  let ctrace := (U z)^2 *
    (deriv (exteriorForwardGerm F) (conj z) /
      (actualHarmonic F z)^2).re
  have hK : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hP0' := hP0 i hreg hlevel
  have hR0' := hR0 i hreg hlevel fp
  have hS0' := hS0 i hreg hlevel
  have hchi := hchi0 i hreg hlevel cp
  have hchiDeriv := (hcomp i hreg hlevel).1.fderiv
  have hsigmaDeriv := (hcomp i hreg hlevel).2.2.fderiv
  dsimp only at hP0' hR0' hS0' hchi ⊢
  have hChiZero : cp * ((k : ℝ) * u * Ur + t z * ugrad) = 0 := by
    simp only [chi, ugrad, U, ux, uy, t, hchiDeriv,
      zero_apply, zero_mul, zero_add, mul_zero] at hchi
    linarith
  have hSigmaZero : sigmaGrad = 0 := by
    simp [sigmaGrad, t, hsigmaDeriv]
  have hP : actualEnergyFluxPdiv F k beta z =
      chi * (ux^2 + uy^2) + chi * (U z *
        actualHarmonicPhaseLaplacian F k beta z) -
        cp * ((k : ℝ) * u * Ur + t z * ugrad) := by
    dsimp only [chi, U, ux, uy] at hP0' ⊢
    rw [hP0', hChiZero]
    ring
  have hR : actualEnergyFluxRdiv F k beta z =
      (y z / ‖z‖ * f - (f + t z * fp) * yr - (k : ℝ) * fp) * u^2 +
      2 * f * u * Ur := by
    simpa only [f, t, y, u, yr, Ur, U] using hR0'
  have hS : actualEnergyFluxSdiv F k beta z =
      2 * sigma * drift + sigmaGrad - 2 * sigma * ctrace := by
    dsimp only [sigma, drift, ctrace, Q, U, ux, uy] at hS0' ⊢
    rw [hSigmaZero]
    nlinarith [hS0']
  have hPDE0 := actualHarmonicPhase_fluxPS_drift_cancellation
    F hc k hk beta chi sigma hz hH
  have hPDE : chi * (U z * actualHarmonicPhaseLaplacian F k beta z) -
      4 * ((k : ℝ) - 1) * sigma * drift =
      4 * ((k : ℝ) - 1) * (chi - sigma) * drift -
        4 * (k : ℝ) * ((k : ℝ) - 1) * chi * u^2 := by
    convert hPDE0 using 1 <;> ring
  have hledger := energyFlux_signed_ledger
    (K := (k : ℝ)) (χ := chi) (f := f) (σ := sigma)
    (t := t z) (cp := cp) (fp := fp)
    (p2 := ux^2 + uy^2) (u := u) (drift := drift)
    (ur := Ur) (yr := yr) (yOverR := y z / ‖z‖)
    (ugrad := ugrad) (sigmaGrad := sigmaGrad)
    (ctrace := ctrace)
    (lap := U z * actualHarmonicPhaseLaplacian F k beta z)
    (P := actualEnergyFluxPdiv F k beta z)
    (R := actualEnergyFluxRdiv F k beta z)
    (S := actualEnergyFluxSdiv F k beta z)
    hK hP hR hS hPDE
  simpa only [actualEnergyFluxDiv] using hledger

end
end SpringerLean

#print axioms SpringerLean.actualEnergyFlux_signed_ledger_knot_ae
