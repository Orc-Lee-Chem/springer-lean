import SpringerLean.Round1651WeightedDerivativeTransferGeneral

open scoped ComplexConjugate

namespace SpringerLean

/-- The exact actual antiholomorphic derivative cost appearing in the
energy multiplier coefficient B. -/
theorem actualHarmonicPhase_antiholomorphic_cost_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 1 ≤ k)
    (beta : ℂ) (hbeta : ‖beta‖ = 1)
    {z : ℂ} (hz : ‖z‖ < 1)
    (hH : actualHarmonic F z ≠ 0) :
    let U := actualHarmonicPhaseField F k beta
    let y := ‖actualHarmonic F z‖
    let p := Real.sqrt
      (((fderiv ℝ U z) (1:ℂ))^2+
       ((fderiv ℝ U z) Complex.I)^2)
    ‖deriv (exteriorForwardGerm F) (conj z)‖*(U z/y)^2 ≤
      (U z/y)^2 + |U z/y| * p/(k:ℝ) := by
  let U := actualHarmonicPhaseField F k beta
  let y := ‖actualHarmonic F z‖
  let p := Real.sqrt
    (((fderiv ℝ U z) (1:ℂ))^2+
     ((fderiv ℝ U z) Complex.I)^2)
  let q := |U z/y|
  let Y := y^(k-1)
  have hkR : (0:ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hy : 0 < y := norm_pos_iff.mpr hH
  have hY : 0 < Y := pow_pos hy _
  have hq : 0 ≤ q := abs_nonneg _
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hqY : q ≤ Y :=
    actualHarmonicPhase_quotient_abs_le F k hk beta hbeta z hH
  have hweighted := actualHarmonicPhaseField_deriv_norm_linear_bound
    F hc k beta hbeta hz
  have hweighted' : (k:ℝ)*Y*
      ‖deriv (exteriorForwardGerm F) (conj z)‖ ≤
      (1:ℝ)*(k:ℝ)*Y+p := by
    simpa only [one_mul] using hweighted
  have htrans := weighted_derivative_transfer_general
    (C := 1) hkR hY hq hqY hp hweighted'
  have hmul := mul_le_mul_of_nonneg_left htrans hq
  have hq2 : q^2 = (U z/y)^2 := sq_abs _
  dsimp only at ⊢
  rw [← hq2]
  change ‖deriv (exteriorForwardGerm F) (conj z)‖*q^2 ≤
    q^2+q*p/(k:ℝ)
  calc
    ‖deriv (exteriorForwardGerm F) (conj z)‖*q^2 =
        q*(q*‖deriv (exteriorForwardGerm F) (conj z)‖) := by ring
    _ ≤ q*(1*q+p/(k:ℝ)) := hmul
    _ = q^2+q*p/(k:ℝ) := by ring

end SpringerLean

#print axioms SpringerLean.actualHarmonicPhase_antiholomorphic_cost_le
