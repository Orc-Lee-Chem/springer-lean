import SpringerLean.Round1864CosineGammaEvaluation
import SpringerLean.Round1857ChebyshevDerivativeMomentLimit

open MeasureTheory Filter Set
open scoped Topology

namespace SpringerLean

theorem integral_abs_cos_rpow_eq_two_half (p : ℝ) (hp : 0 < p) :
    (∫ θ in (0 : ℝ)..Real.pi, |Real.cos θ| ^ p) =
      2 * (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p) := by
  let f : ℝ → ℝ := fun θ => |Real.cos θ| ^ p
  have hcont : Continuous f :=
    (Real.continuous_rpow_const hp.le).comp (by fun_prop)
  have hmirror : (∫ θ in (Real.pi / 2)..Real.pi, f θ) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), f θ := by
    have hsub := intervalIntegral.integral_comp_sub_left f Real.pi
      (a := 0) (b := Real.pi / 2)
    have he : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
    rw [he, sub_zero] at hsub
    rw [← hsub]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [f, Real.cos_pi_sub, abs_neg]
  have hfirst : (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ) =
      ∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hh : θ ∈ Icc (0 : ℝ) (Real.pi / 2) := by
      simpa only [uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)] using hθ
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hh.1, Real.pi_pos], hh.2⟩
    simp only [f, abs_of_nonneg hc]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (0 : ℝ) (Real.pi / 2))
    (hcont.intervalIntegrable (μ := volume) (Real.pi / 2) Real.pi)
  change (∫ θ in (0 : ℝ)..Real.pi, f θ) = _
  rw [← hadd, hmirror, hfirst]
  ring

theorem arcsineRadialMomentIntegral_eq_slit_constant (p : ℝ) (hp : 0 < p) :
    arcsineRadialMomentIntegral p = slitRadialMomentConstant p := by
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun θ : ℝ => |Real.cos θ| ^ p) Real.pi_ne_zero (a := 0) (b := 1)
  simp only [mul_zero, mul_one, smul_eq_mul] at hsub
  rw [arcsineRadialMomentIntegral, hsub, integral_abs_cos_rpow_eq_two_half p hp]
  have he : (2 : ℝ) ^ p * (Real.pi⁻¹ *
      (2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p)) =
      (2 : ℝ) ^ (p + 1) / Real.pi *
        (∫ θ in (0 : ℝ)..(Real.pi / 2), (Real.cos θ) ^ p) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  rw [he]
  exact normalized_cosine_half_integral_eq_slit_constant p hp

/-- The exact gamma limit for each fixed derivative order and every
positive real exponent, with the original capacity normalization. -/
theorem monicChebyshevDerivativeRadialMoment_tendsto_slit_constant
    (j : ℕ) (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ => monicChebyshevDerivativeRadialMoment n j p)
      atTop (𝓝 (slitRadialMomentConstant p)) := by
  rw [← arcsineRadialMomentIntegral_eq_slit_constant p hp]
  exact monicChebyshevDerivativeRadialMoment_tendsto j p hp

end SpringerLean

#print axioms SpringerLean.arcsineRadialMomentIntegral_eq_slit_constant
#print axioms SpringerLean.monicChebyshevDerivativeRadialMoment_tendsto_slit_constant
