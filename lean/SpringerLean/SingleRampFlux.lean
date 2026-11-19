import SpringerLean.SingleRamp
import SpringerLean.ReviewChecks
import SpringerLean.Round1696LipschitzFlatComposition
import SpringerLean.Round1749ActualFluxAmplitudesLocalLipschitz
import SpringerLean.Round1750LocalLipschitzOperations
import SpringerLean.Round1751ActualPhaseGradientC1

open Filter MeasureTheory
open scoped Topology

namespace SpringerLean.AnalyticRevision

noncomputable section

def ramp (t : ℝ) : ℝ := min (12 * t) (9/5)

def rampSlope (t : ℝ) : ℝ := if t ≤ 3/20 then 12 else 0

theorem ramp_lipschitz : LipschitzWith 12 ramp := by
  have h : LipschitzWith 12 (fun t : ℝ => (12 : ℝ) * t) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simp only [Real.dist_eq, ← mul_sub, abs_mul]
    norm_num
  exact h.min_const _

theorem ramp_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ ramp t ∧ ramp t ≤ 9/5 ∧ ramp t ≤ 12*t :=
  ⟨le_min (by positivity) (by norm_num), min_le_right _ _, min_le_left _ _⟩

def rampA (K t : ℝ) : ℝ :=
  let χ := ramp t
  let cp := rampSlope t
  let f := χ/6
  let fp := cp/6
  χ+fp-(2*f+2*|f+t*fp|)/K

def rampB (K t : ℝ) : ℝ :=
  let χ := ramp t
  let cp := rampSlope t
  let f := χ/6
  let fp := cp/6
  χ+|2*f-K*cp/(4*(K-1))|+t*|cp|/(2*(K-1))+|f+t*fp|/K

def rampD (K t : ℝ) : ℝ :=
  (K*ramp t+t*|rampSlope t|)/(4*(K-1))

/-- The two multiplier pieces in the homogeneous form needed by the
actual phase field, including zero gradient. -/
theorem ramp_homogeneous (K t u p : ℝ) (hK : 751 ≤ K) (ht : 0 ≤ t)
    (hp : 0 ≤ p) :
    rampD K t*p^2+K*rampB K t*|u| * p-K^2*(rampA K t-1)*u^2 ≤ (7/3)*p^2 := by
  have hK₀ : 0 < K := by linarith
  have hK₁ : (1:ℝ) ≤ K := by linarith
  refine SpringerAnalyticReview.homogeneousFlux _ _ _ _ _ _ ?_ hK₀.le hp ?_
  · apply sub_nonneg.mpr
    by_cases h : t ≤ 3/20
    · have hχ : ramp t = 12*t := min_eq_left (by linarith)
      have hh : 0 ≤ 12*t/6 + t*(12/6) := by positivity
      have hdiv : (2*(12*t/6) + 2*(12*t/6+t*(12/6)))/K ≤ 12*t := by
        apply (div_le_iff₀ hK₀).mpr
        nlinarith [mul_nonneg (sub_nonneg.mpr hK₁) ht]
      simp only [rampA, rampSlope, ite_eq_left h, hχ, abs_of_nonneg hh]
      linarith
    · have hχ : ramp t = 9/5 := min_eq_right (by linarith)
      have hdiv : (6/5:ℝ)/K ≤ 4/5 := by
        apply (div_le_iff₀ hK₀).mpr
        linarith
      norm_num [rampA, rampSlope, h, hχ, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 9/5/6)]
      linarith
  · intro q hq
    exact SingleRamp.clippedLinearFlux K t q hK ht hq

def rampFluxP (F : ℂ → ℂ) (k : ℕ) (β z : ℂ) : ℂ :=
  let U := actualHarmonicPhaseField F k β
  let χ := ramp (actualHarmonicMultiplierTime F k z)
  Complex.mk (χ*U z*(fderiv ℝ U z) (1:ℂ))
    (χ*U z*(fderiv ℝ U z) Complex.I)

def rampFluxR (F : ℂ → ℂ) (k : ℕ) (β z : ℂ) : ℂ :=
  let U := actualHarmonicPhaseField F k β
  let f := ramp (actualHarmonicMultiplierTime F k z)/6
  let a := f*(U z)^2/‖actualHarmonic F z‖
  Complex.mk (a*z.re/‖z‖) (a*z.im/‖z‖)

/-- The single-ramp flux χ U ∇U + 4(k−1)eᵣ f U²/|H|, with f = χ/6. -/
def rampFlux (F : ℂ → ℂ) (k : ℕ) (β z : ℂ) : ℂ :=
  rampFluxP F k β z + (4*((k:ℝ)-1)) • rampFluxR F k β z

/-- Both pieces are differentiated with the same slope. The physical
time is flat almost everywhere on the cutoff level itself. -/
theorem ramp_hasFDerivAt_ae (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) :
    ∀ᵐ z ∂(volume : Measure ℂ),
      z ∈ actualMultiplierRegularSet F →
      HasFDerivAt (fun w => ramp (actualHarmonicMultiplierTime F k w))
        (rampSlope (actualHarmonicMultiplierTime F k z) •
          fderiv ℝ (actualHarmonicMultiplierTime F k) z) z := by
  filter_upwards [actualHarmonicMultiplierTime_ae_fderiv_zero_on_level
    F hc k (3/20)] with z hflat hreg
  obtain ⟨hz, hH, hz₀⟩ := (actualMultiplierRegularSet_mem_iff F z).mp hreg
  let t := actualHarmonicMultiplierTime F k
  have hcd := actualHarmonicMultiplierTime_contDiffAt_regular F hc k hz hz₀ hH
  have hd : DifferentiableAt ℝ t z := hcd.differentiableAt (by simp)
  change HasFDerivAt (fun w => ramp (t w)) (rampSlope (t z) • fderiv ℝ t z) z
  rcases lt_trichotomy (t z) (3/20) with h | h | h
  · have heq : (fun w => ramp (t w)) =ᶠ[𝓝 z] (fun w => (12:ℝ)*t w) := by
      filter_upwards [hd.continuousAt.eventually (gt_mem_nhds h)] with w hw
      change t w < 3/20 at hw
      exact min_eq_left (by linarith)
    simpa only [rampSlope, ite_eq_left h.le] using
      (hd.hasFDerivAt.const_mul 12).congr_of_eventuallyEq heq
  · have hzflat : fderiv ℝ t z = 0 := hflat hreg h
    have hd₀ : HasFDerivAt t (0 : ℂ →L[ℝ] ℝ) z := by
      simpa only [hzflat] using hd.hasFDerivAt
    simpa only [hzflat, smul_zero] using
      lipschitz_comp_hasFDerivAt_zero t ramp z hd₀ ramp_lipschitz
  · have heq : (fun w => ramp (t w)) =ᶠ[𝓝 z] (fun _ : ℂ => (9/5:ℝ)) := by
      filter_upwards [hd.continuousAt.eventually (lt_mem_nhds h)] with w hw
      change 3/20 < t w at hw
      exact min_eq_right (by linarith)
    simpa only [rampSlope, ite_eq_right (not_le.mpr h), zero_smul] using
      (hasFDerivAt_const (9/5:ℝ) z).congr_of_eventuallyEq heq

end
end SpringerLean.AnalyticRevision
