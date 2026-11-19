import SpringerLean.Round1777AlignedAngularScalar
import SpringerLean.Round1773ActualSignedPhaseIntegral

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 600000

/-- Exact polar algebra at either sign of a sine-zero phase ray. -/
theorem phaseRay_power_im_sq
    (beta v : ℂ) (k : ℕ) (hphase : (beta*v^k)^2=1)
    (r θ : ℝ) :
    (beta*(v*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))^k).im^2=
      r^(2*k)*(Real.sin ((k : ℝ)*θ))^2 := by
  have hexp : Complex.exp ((θ : ℂ)*Complex.I)^k=
      Complex.exp ((((k : ℝ)*θ : ℝ) : ℂ)*Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfactor : beta*(v*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))^k=
      (beta*v^k)*(r : ℂ)^k*Complex.exp ((((k : ℝ)*θ : ℝ) : ℂ)*Complex.I) := by
    rw [mul_pow, mul_pow, hexp]
    ring
  rw [hfactor]
  rcases sq_eq_one_iff.mp hphase with hp | hp <;>
    rw [hp] <;>
    simp [Complex.exp_mul_I, Complex.mul_im, ← Complex.ofReal_pow,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_mul, pow_mul] <;> ring

theorem aligned_complex_phase_cost_le_projection
    (beta v w : ℂ) (hv : ‖v‖=1) (k : ℕ) (hk : 751 ≤ k)
    (hphase : (beta*v^k)^2=1) {r θ : ℝ} (hr : 0 < r)
    (hw : w=v*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
    (hθ : |(k : ℝ)*θ| ≤ 14/5) :
    ‖w‖^(2*k-2)-(8/25 : ℝ)*((beta*w^k).im^2/‖w‖^2) ≤
      ((conj v*w).re)^(2*k-2) := by
  have hnorm : ‖w‖=r := by
    rw [hw, norm_mul, norm_mul, hv, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    ring
  have hvv : conj v*v=1 := by simp [RCLike.conj_mul, hv]
  have hproj : (conj v*w).re=r*Real.cos θ := by
    have hh : conj v*w=(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
      rw [hw]
      calc
        _ = (conj v*v)*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by ring
        _ = _ := by rw [hvv, one_mul]
    rw [hh]
    simp [Complex.exp_mul_I, Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have him := phaseRay_power_im_sq beta v k hphase r θ
  rw [← hw] at him
  have hrpow : r^(2*k)=r^(2*k-2)*r^2 := by
    rw [← pow_add]
    congr 1
    omega
  have hpot : (beta*w^k).im^2/‖w‖^2=r^(2*k-2)*(Real.sin ((k : ℝ)*θ))^2 := by
    rw [him, hnorm, hrpow]
    field_simp [hr.ne']
  rw [hpot, hnorm, hproj, mul_pow]
  have hs := aligned_phase_penalty_pays_projection hk (by omega : 2*k-2 ≤ 2*k) hθ
  have hh := mul_le_mul_of_nonneg_left hs (pow_nonneg hr.le (2*k-2))
  nlinarith

/-- Actual-F pointwise domination once the geometric aligned cone
and positive projection have been established. -/
theorem actualSignedPhaseDensity_le_projected_of_aligned_polar
    (F : ℂ → ℂ) (beta v z : ℂ) (hv : ‖v‖=1) (k : ℕ) (hk : 751 ≤ k)
    (hphase : (beta*v^k)^2=1) {r θ : ℝ} (hr : 0 < r)
    (hw : actualHarmonic F z=v*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I))
    (hθ : |(k : ℝ)*θ| ≤ 14/5)
    (hx : 0 ≤ (conj v*actualHarmonic F z).re) :
    actualSignedPhaseDensity F k beta z ≤
      (max ((conj v*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) := by
  unfold actualSignedPhaseDensity actualHarmonicPhasePotentialDensity actualHarmonicPhaseField
  rw [max_eq_left hx]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact aligned_complex_phase_cost_le_projection beta v (actualHarmonic F z) hv k hk hphase hr hw hθ

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_le_projected_of_aligned_polar
