import SpringerLean.Round1806TrueAxisSignedPower
import SpringerLean.Round1805RelativePhasePower
import SpringerLean.Round1804ActualTrueAxisAngles
import SpringerLean.Round1798TrueAxisLambdaLog

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 1200000

/-- Actual nonaligned pointwise comparison in the true endpoint axis.
The actual strip controls the angular cost, the recorded phase ray
supplies its phase, and the fixed moment-ratio factor pays for it. -/
theorem actualSignedPhaseDensity_trueAxis_lt_lower_power
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδlo : Real.pi/3 ≤ |(k : ℝ)*δ|) (hδhi : |(k : ℝ)*δ| ≤ Real.pi/2)
    (z : ℂ) (hz : ‖z‖ < 1)
    (hx : (9/5 : ℝ) ≤ (conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re) :
    actualSignedPhaseDensity F k beta z <
      trueAxisMomentRatioLambda ((2*k-2 : ℕ) : ℝ)*
        (max ((conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re/2) 0)^(2*k-10) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let ξ := P/(‖P‖ : ℂ)
  let w := actualHarmonic F z
  let Z := conj ξ*w
  let x := Z.re
  let u := x/2
  let s := m*(1-u)
  let h := |Z.im|/x
  let gamma := (k : ℝ)*δ
  let theta := (k : ℝ)*Complex.arg Z
  let Lambda := trueAxisMomentRatioLambda m
  have hm : (1500 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have hx0 : 0 < x := by dsimp [x, Z, ξ, w]; linarith
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hnorm : ‖Z‖=‖w‖ := by dsimp [Z]; rw [norm_mul, Complex.norm_conj, hξ, one_mul]
  have hx2 : x ≤ 2 := by
    calc
      x ≤ ‖Z‖ := Complex.re_le_norm _
      _ = ‖w‖ := hnorm
      _ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc (actualHarmonic_mem_convexHull_omitted F hc hz)
  have hs0 : 0 ≤ s := mul_nonneg hm0.le (by dsimp [u]; linarith)
  obtain ⟨hcost,hshort⟩ := exteriorOmitted_actualEndpoint_trueAxis_angles F hc k hk P hP hd ht hW z hz hx
  change m^2*h^2/2 ≤ 1/6+(5/8 : ℝ)*s at hcost
  change (s ≤ 2 → |theta| ≤ 6/7) at hshort
  obtain ⟨hLambda,hlogLambda⟩ := trueAxisMomentRatioLambda_pos_and_log hm
  have hmn : m=2*((k-1 : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast (by omega : 2*k-2=2*(k-1))
  have hp := trueAxis_signed_power_lt_lower (k-1) (by omega : 750 ≤ k-1)
    hu0 hs0 (by rw [←hmn]) hLambda
    (by rw [←hmn]; exact hlogLambda) (by rw [←hmn]; exact hcost)
    hδlo hδhi hshort
  have hexp : 2*(k-1)=2*k-2 := by omega
  have hexp' : 2*k-2-8=2*k-10 := by omega
  rw [hexp, hexp'] at hp
  have hr : 0 < ‖w‖ := by
    have hh := Complex.re_le_norm Z
    rw [hnorm] at hh
    exact hx0.trans_le hh
  have hpot := actualHarmonicPhasePotentialDensity_relative_polar F k (by omega : 1 ≤ k)
    beta ξ v hξ δ hv hphase z hr
  change actualHarmonicPhasePotentialDensity F k beta z=
    ‖w‖^(2*k-2)*(Real.sin (gamma-theta))^2 at hpot
  have hnorm2 : ‖w‖^2=x^2+Z.im^2 := by
    rw [←hnorm, Complex.sq_norm]
    simp only [Complex.normSq_apply, x, pow_two]
  have hf2 : ‖w‖^2=x^2*(1+h^2) := by
    rw [hnorm2]
    dsimp [h]
    rw [div_pow, sq_abs]
    field_simp [hx0.ne']
    <;> ring
  have hfraw : ‖w‖^(2*(k-1))=x^(2*(k-1))*(1+h^2)^(k-1) := by
    rw [pow_mul, hf2, mul_pow, ←pow_mul]
  have hf : ‖w‖^(2*k-2)/(2 : ℝ)^(2*k-2)=u^(2*k-2)*(1+h^2)^(k-1) := by
    rw [←hexp, hfraw]
    dsimp [u]
    conv_rhs => rw [div_pow]
    ring
  have hdensity : actualSignedPhaseDensity F k beta z=
      u^(2*k-2)*(1+h^2)^(k-1)*(1-(8/25 : ℝ)*(Real.sin (gamma-theta))^2) := by
    unfold actualSignedPhaseDensity
    rw [hpot]
    change (‖w‖^(2*k-2)-(8/25 : ℝ)*(‖w‖^(2*k-2)*(Real.sin (gamma-theta))^2))/(2 : ℝ)^(2*k-2)=_
    have heq : (‖w‖^(2*k-2)-(8/25 : ℝ)*(‖w‖^(2*k-2)*(Real.sin (gamma-theta))^2))/(2 : ℝ)^(2*k-2)=
        (‖w‖^(2*k-2)/(2 : ℝ)^(2*k-2))*(1-(8/25 : ℝ)*(Real.sin (gamma-theta))^2) := by ring
    rw [heq,hf]
  change actualSignedPhaseDensity F k beta z < Lambda*(max u 0)^(2*k-10)
  rw [hdensity,max_eq_left hu0.le]
  exact hp

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_trueAxis_lt_lower_power
