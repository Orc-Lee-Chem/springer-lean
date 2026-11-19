import SpringerLean.SingleRampFlux
import SpringerLean.Round1614ActualPhaseFluxR
import SpringerLean.Round1644SourceRadiusCartesianDerivative
import SpringerLean.Round1667SignedFluxLedger
import SpringerLean.Round1671ActualMixedCrossCosts
import SpringerLean.Round1672ActualRadialModulusCost
import SpringerLean.Round1673ActualChiGradientCost
import SpringerLean.Round1661ActualRadialPositivePart
import SpringerLean.Round1733CartesianDivergenceLinear

open scoped ComplexConjugate

namespace SpringerLean.AnalyticRevision

noncomputable section

/-- The local \(7/3\) inequality for the actual ramp flux wherever
the physical multiplier obeys its slope rule. -/
theorem ramp_pointwise_regular
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (β : ℂ) (hβ : ‖β‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1) (hz₀ : z ≠ 0) (hH : actualHarmonic F z ≠ 0)
    (hχ : HasFDerivAt (fun w => ramp (actualHarmonicMultiplierTime F k w))
      (rampSlope (actualHarmonicMultiplierTime F k z) •
        fderiv ℝ (actualHarmonicMultiplierTime F k) z) z) :
    DifferentiableAt ℝ (rampFlux F k β) z ∧
    (k:ℝ)^2 * actualHarmonicPhasePotentialDensity F k β z +
      (k:ℝ)/(4*((k:ℝ)-1)) * actualCartesianDiv (rampFlux F k β) z ≤
        (7/3 : ℝ) *
          (((fderiv ℝ (actualHarmonicPhaseField F k β) z) (1:ℂ))^2 +
            ((fderiv ℝ (actualHarmonicPhaseField F k β) z) Complex.I)^2) := by
  let K : ℝ := k
  let t := actualHarmonicMultiplierTime F k
  let χ : ℂ → ℝ := fun w => ramp (t w)
  let f : ℂ → ℝ := fun w => χ w/6
  let cp := rampSlope (t z)
  let fp := cp/6
  let U := actualHarmonicPhaseField F k β
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let ux := fderiv ℝ U z (1:ℂ)
  let uy := fderiv ℝ U z Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let u := U z/y z
  let b := K/(4*(K-1))
  let Q := (conj (actualHarmonic F z))⁻¹
  let Ur := fderiv ℝ U z (z/‖z‖)
  let yr := fderiv ℝ y z (z/‖z‖)
  let drift := U z*(Q.re*ux+Q.im*uy)
  let ugrad := u*(fderiv ℝ y z (1:ℂ)*ux+fderiv ℝ y z Complex.I*uy)
  have hk2 : 2 ≤ k := by omega
  have hK : 751 ≤ K := by
    change (751:ℝ) ≤ (k:ℝ)
    exact_mod_cast hk
  have hK₀ : K ≠ 0 := by linarith
  have hK₁ : K-1 ≠ 0 := by linarith
  have ht : 0 ≤ t z := actualHarmonicMultiplierTime_nonneg F k hz
  have hχ₀ : 0 ≤ χ z := (ramp_bounds ht).1
  have hf₀ : 0 ≤ f z := by dsimp [f]; positivity
  have hy₀ : y z ≠ 0 := norm_ne_zero_iff.mpr hH
  have hp : p^2 = ux^2+uy^2 := Real.sq_sqrt (by positivity)
  have hχ' (v : ℂ) : fderiv ℝ χ z v = cp * fderiv ℝ t z v := by
    change fderiv ℝ χ z v = _
    rw [hχ.fderiv]
    rfl
  have hf : HasFDerivAt f (fp • fderiv ℝ t z) z := by
    convert hχ.const_mul ((6:ℝ)⁻¹) using 1
    · ext w
      dsimp [f,χ,t]
      ring
    · rw [smul_smul]
      change fp • fderiv ℝ t z = (6⁻¹ * cp) • fderiv ℝ t z
      congr 1
      dsimp [fp]
      ring
  have hf' : fderiv ℝ f z (z/‖z‖) = fp * fderiv ℝ t z (z/‖z‖) := by
    rw [hf.fderiv]
    rfl
  have htime (v : ℂ) := actualHarmonicMultiplierTime_fderiv F hc k hz hz₀ hH v
  have hr := source_radius_fderiv_coordinates hz₀
  have hUr := fderiv_radial_cartesian U z hz₀
  have hgrad :
      U z*(fderiv ℝ χ z (1:ℂ)*ux+fderiv ℝ χ z Complex.I*uy) =
        -cp*(K*u*Ur+t z*ugrad) := by
    rw [hχ', hχ', htime, htime, hr.1, hr.2]
    dsimp only [u, ugrad, Ur, ux, uy]
    rw [hUr]
    dsimp only [K, t, y] at hy₀ ⊢
    field_simp [hy₀, norm_ne_zero_iff.mpr hz₀]
    ring
  have hP : actualCartesianDiv (rampFluxP F k β) z =
      χ z*p^2+χ z*(U z*actualHarmonicPhaseLaplacian F k β z)-
        cp*(K*u*Ur+t z*ugrad) := by
    have h := actualHarmonic_phaseFluxP_divergence F hc k β χ hz hχ.differentiableAt
    dsimp only at h
    change actualCartesianDiv (rampFluxP F k β) z = _ at h
    rw [h, hp]
    change χ z*(ux^2+uy^2)+χ z*U z*actualHarmonicPhaseLaplacian F k β z+
        U z*(fderiv ℝ χ z (1:ℂ)*ux+fderiv ℝ χ z Complex.I*uy) = _
    rw [hgrad]
    ring
  have hR : actualCartesianDiv (rampFluxR F k β) z =
      (y z/‖z‖*f z-(f z+t z*fp)*yr-K*fp)*u^2 + 2*f z*u*Ur :=
    actualHarmonic_phaseFluxR_divergence F hc k β f fp hz hz₀ hH
      hf.differentiableAt hf'
  have hU := (actualHarmonicPhaseField_hasFDerivAt F hc k β hz).differentiableAt
  obtain ⟨hUx,hUy⟩ := actualHarmonicPhase_gradient_coordinates_differentiableAt
    F hc k β hz
  have hPd : DifferentiableAt ℝ (rampFluxP F k β) z := by
    change DifferentiableAt ℝ
      (fun w => Complex.mk (χ w*U w*fderiv ℝ U w (1:ℂ))
        (χ w*U w*fderiv ℝ U w Complex.I)) z
    exact complex_mk_differentiableAt_of_coordinates _ _ z ((hχ.differentiableAt.mul hU).mul hUx)
      ((hχ.differentiableAt.mul hU).mul hUy)
  have hRd : DifferentiableAt ℝ (rampFluxR F k β) z := by
    have ha : DifferentiableAt ℝ (fun w => f w*(U w)^2/y w) z :=
      (hf.differentiableAt.mul (hU.pow 2)).mul
        ((actualHarmonic_norm_differentiableAt F hc hz hH).inv hy₀)
    have hr := source_radius_differentiableAt hz₀
    have hr' := hr.inv (norm_ne_zero_iff.mpr hz₀)
    exact complex_mk_differentiableAt_of_coordinates _ _ z
      ((ha.mul Complex.reCLM.differentiableAt).mul hr')
      ((ha.mul Complex.imCLM.differentiableAt).mul hr')
  refine ⟨hPd.add (hRd.const_smul (4*(K-1))), ?_⟩
  have hdiv : actualCartesianDiv (rampFlux F k β) z =
      actualCartesianDiv (rampFluxP F k β) z +
        4*(K-1)*actualCartesianDiv (rampFluxR F k β) z := by
    change actualCartesianDiv (fun w => rampFluxP F k β w + (4*(K-1)) •
      rampFluxR F k β w) z = _
    rw [actualCartesianDiv_add (rampFluxP F k β)
      (fun w => (4*(K-1)) • rampFluxR F k β w) z hPd (hRd.const_smul (4*(K-1))),
      actualCartesianDiv_real_smul (4*(K-1)) (rampFluxR F k β) z hRd]
  have hPDE : χ z*(U z*actualHarmonicPhaseLaplacian F k β z) =
      4*(K-1)*χ z*drift - 4*K*(K-1)*χ z*u^2 := by
    simpa only [K, u, y, drift, Q, U, ux, uy, mul_zero, zero_mul, sub_zero] using
      (actualHarmonicPhase_fluxPS_drift_cancellation F hc k hk2 β (χ z) 0 hz hH)
  have hledger := energyFlux_signed_ledger
    K (χ z) (f z) 0 (t z) cp fp (p^2) u drift Ur yr (y z/‖z‖) ugrad 0 0
    (U z*actualHarmonicPhaseLaplacian F k β z)
    (actualCartesianDiv (rampFluxP F k β) z)
    (actualCartesianDiv (rampFluxR F k β) z) 0
    (by linarith) hP hR (by simp) (by simpa using hPDE)
  simp only [mul_zero, sub_zero, add_zero] at hledger
  change b*_ = _ at hledger
  rw [← hdiv] at hledger
  have hDrift := actualHarmonicPhase_drift_cross_cost_le F k β z (χ z)
  have hRadial := actualHarmonicPhase_radial_cross_cost_le F k β hz₀ (2*f z-b*cp)
  have hYr := actualHarmonicPhase_radial_modulus_cost_le F hc k (by omega)
    β hβ hz hz₀ hH (f z+t z*fp)
  have hChi := actualHarmonicPhase_chi_gradient_cost_le F hc k hk2 β hβ hz hH cp
  have hGeom := actualHarmonic_radial_multiplier_positivePart_le F hc hz hz₀ (f z)
  rw [max_eq_right hf₀] at hGeom
  have hGeom' : K*(y z/‖z‖)*f z*u^2 ≤ 2*K*f z*u^2 := by
    have hm := mul_le_mul_of_nonneg_right hGeom
      (show 0 ≤ K*u^2 by dsimp [K]; positivity)
    change (y z/‖z‖)*f z*(K*u^2) ≤ 2*f z*(K*u^2) at hm
    nlinarith only [hm]
  have hD : rampD K (t z) = b*χ z+(b/K)*t z*|cp| := by
    dsimp only [rampD, b, χ, cp]
    field_simp [hK₀, hK₁]
  have hB : rampB K (t z) =
      χ z+|2*f z-b*cp|+2*(b/K)*t z*|cp|+|f z+t z*fp|/K := by
    dsimp only [rampB, b, χ, f, cp, fp]
    field_simp [hK₀, hK₁]
    ring
  have hA : rampA K (t z) = χ z+fp-(2*f z+2*|f z+t z*fp|)/K := rfl
  have hd : K*χ z*drift ≤ K*χ z*|u| * p := by
    simpa only [abs_of_nonneg hχ₀] using hDrift
  let a := f z+t z*fp
  have hABD : K^2*rampA K (t z)*u^2+b*actualCartesianDiv (rampFlux F k β) z ≤
      rampD K (t z)*p^2+K*rampB K (t z)*|u| * p := by
    calc
      _ ≤ K^2*rampA K (t z)*u^2 +
          (b*χ z*p^2-K^2*(χ z+fp)*u^2+
            K*χ z*|u| * p+K*|2*f z-b*cp| * |u| * p+
            (2*K*|a| * u^2+|a| * |u| * p)+2*K*f z*u^2+
            (2*b*t z*|cp| * |u| * p+(b/K)*t z*|cp| * p^2)) := by
        rw [hledger]
        change K*(2*f z-b*cp)*u*Ur ≤ K*|2*f z-b*cp| * |u| * p at hRadial
        change -K*a*yr*u^2 ≤ 2*K*|a| * u^2+|a| * |u| * p at hYr
        have hChi' : -b*cp*t z*ugrad ≤
            2*b*t z*|cp| * |u| * p+(b/K)*t z*|cp| * p^2 := by
          simpa only [ugrad,mul_assoc] using hChi
        dsimp only [b] at hRadial hChi' ⊢
        linarith only [hd, hRadial, hYr, hGeom', hChi']
      _ = _ := by
        rw [hA, hB, hD]
        change K^2*(χ z+fp-(2*f z+2*|a|)/K)*u^2+_ =
          (b*χ z+(b/K)*t z*|cp|)*p^2+
          K*(χ z+|2*f z-b*cp|+2*(b/K)*t z*|cp|+|a|/K)*|u| * p
        field_simp [hK₀]
        ring
  have hs := ramp_homogeneous K (t z) u p hK ht (Real.sqrt_nonneg _)
  change K^2*((U z)^2/(y z)^2) + b*actualCartesianDiv (rampFlux F k β) z ≤
    (7/3)*(ux^2+uy^2)
  rw [← div_pow, ← hp]
  change K^2*u^2+b*actualCartesianDiv (rampFlux F k β) z ≤ _
  linarith only [hABD, hs]

end
end SpringerLean.AnalyticRevision
