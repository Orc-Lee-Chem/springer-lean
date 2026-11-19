import SpringerLean.Round1665SigmaGradientScalarCost
import SpringerLean.Round1664ActualSigmaTraceCost
import SpringerLean.Round1659InverseDriftScalarProjection

open scoped ComplexConjugate

namespace SpringerLean

/-- The actual sigma-cutoff derivative is paid by exactly the two
terms entered in the original A and B multiplier coefficients. -/
theorem actualHarmonicPhase_sigma_gradient_cost_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    (i : Fin 21)
    {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0)
    (hH : actualHarmonic F z ≠ 0)
    (hleft : energyMultiplierKnotTime i.castSucc <
      actualHarmonicMultiplierTime F k z)
    (hright : actualHarmonicMultiplierTime F k z <
      energyMultiplierKnotTime i.succ) :
    let U := actualHarmonicPhaseField F k beta
    let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
    let t := actualHarmonicMultiplierTime F k
    let sigma : ℂ → ℝ := fun w => energyMultiplierSigma (t w)
    let sp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).sp
    let Q : ℂ := (conj (actualHarmonic F z))⁻¹
    let ux := (fderiv ℝ U z) (1:ℂ)
    let uy := (fderiv ℝ U z) Complex.I
    let p := Real.sqrt (ux^2+uy^2)
    (-(k:ℝ)/2*(U z)^2 *
      ((fderiv ℝ sigma z) (1:ℂ)*Q.re +
       (fderiv ℝ sigma z) Complex.I*Q.im)) ≤
      ((k:ℝ)^2/2) * abs sp * (U z/y z)^2 +
      (k:ℝ)*t z * abs sp * (U z/y z)^2 +
      (t z * abs sp/2) * abs (U z/y z) * p := by
  let U := actualHarmonicPhaseField F k beta
  let y : ℂ → ℝ := fun w => ‖actualHarmonic F w‖
  let t := actualHarmonicMultiplierTime F k
  let sigma : ℂ → ℝ := fun w => energyMultiplierSigma (t w)
  let sp : ℝ := (energyMultiplierEndpointRaw (2*i.val)).sp
  let Q : ℂ := (conj (actualHarmonic F z))⁻¹
  let ux := (fderiv ℝ U z) (1:ℂ)
  let uy := (fderiv ℝ U z) Complex.I
  let p := Real.sqrt (ux^2+uy^2)
  let u := |U z/y z|
  let L := ‖fderiv ℝ y z‖
  let dr := (fderiv ℝ (fun w : ℂ => ‖w‖) z) (1:ℂ)*Q.re +
    (fderiv ℝ (fun w : ℂ => ‖w‖) z) Complex.I*Q.im
  let dy := (fderiv ℝ y z) (1:ℂ)*Q.re +
    (fderiv ℝ y z) Complex.I*Q.im
  have hy : 0 < y z := norm_pos_iff.mpr hH
  have hy0 : y z ≠ 0 := ne_of_gt hy
  have hK : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have ht : 0 ≤ t z := actualHarmonicMultiplierTime_nonneg F k hz
  have hu : 0 ≤ u := abs_nonneg _
  have hR := inverseConjugate_source_radius_fderiv_abs_le
    z (actualHarmonic F z) hz0
  have hY := inverseConjugate_scalar_fderiv_abs_le
    y z (actualHarmonic F z)
  have hR' : |(y z)*dr| ≤ 1 := by
    rw [abs_mul, abs_of_pos hy]
    have hh := mul_le_mul_of_nonneg_left hR (le_of_lt hy)
    have hid : y z*(1/y z) = 1 := by field_simp
    dsimp only [dr, y, Q] at hh ⊢
    nlinarith
  have hY' : |(y z)*dy| ≤ L := by
    rw [abs_mul, abs_of_pos hy]
    have hh := mul_le_mul_of_nonneg_left hY (le_of_lt hy)
    have hid : y z*(L/y z) = L := by field_simp
    dsimp only [dy, L, y, Q] at hh ⊢
    nlinarith
  have hweighted := actualHarmonicPhase_weighted_modulus_gradient_le
    F hc k hk beta hbeta hz hH
  have hcost := sigma_gradient_scalar_cost_le
    (K := (k:ℝ)) (t := t z) (sp := sp) (u := u)
    (p := p) (L := L) (dr := (y z)*dr) (dy := (y z)*dy)
    hK ht hu hR' hY' hweighted
  have hident := actualEnergyMultiplier_sigma_gradient_identity
    F hc k beta i hz hz0 hH hleft hright
  dsimp only at hident hcost ⊢
  have hEq :
      -(k:ℝ)/2*(U z)^2 *
        ((fderiv ℝ sigma z) (1:ℂ)*Q.re +
         (fderiv ℝ sigma z) Complex.I*Q.im) =
      (k:ℝ)/2*sp*((U z)^2/y z)*((k:ℝ)*dr+t z*dy) := by
    calc
      -(k:ℝ)/2*(U z)^2 *
        ((fderiv ℝ sigma z) (1:ℂ)*Q.re +
         (fderiv ℝ sigma z) Complex.I*Q.im) =
        -(k:ℝ)/2*((U z)^2 *
          ((fderiv ℝ sigma z) (1:ℂ)*Q.re +
           (fderiv ℝ sigma z) Complex.I*Q.im)) := by ring
      _ = (k:ℝ)/2*sp*((U z)^2/y z)*((k:ℝ)*dr+t z*dy) := by
        rw [hident]
        ring
  rw [hEq]
  convert hcost using 1
  · rw [sq_abs]
    field_simp [hy0]
  · rw [sq_abs]

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_sigma_gradient_cost_le
