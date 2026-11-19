import SpringerLean.Round739CappedAngularBoundary
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.MeasureTheory.Integral.CircleAverage

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

/-- Cauchy construction for the Poisson extension of continuous real
boundary data. Poisson identification and boundary limits are separate. -/
noncomputable def complexPoissonCauchyExtension (φ : ℂ → ℝ) (w : ℂ) : ℂ :=
  2*(2*Real.pi*Complex.I : ℂ)⁻¹ *
    (∮ ζ in C(0,1), (ζ-w)⁻¹ • (φ ζ : ℂ)) -
      Real.circleAverage (fun ζ => (φ ζ : ℂ)) 0 1

theorem complexPoissonCauchyExtension_analyticOnNhd
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (sphere (0 : ℂ) 1)) :
    AnalyticOnNhd ℂ (complexPoissonCauchyExtension φ) (ball (0 : ℂ) 1) := by
  have hφc : ContinuousOn (fun ζ => (φ ζ : ℂ)) (sphere (0 : ℂ) 1) :=
    Complex.continuous_ofReal.comp_continuousOn hφ
  have hci : CircleIntegrable (fun ζ => (φ ζ : ℂ)) 0 1 := hφc.circleIntegrable (by norm_num)
  have hd : DifferentiableOn ℂ (complexPoissonCauchyExtension φ) (ball (0 : ℂ) 1) := by
    intro w hw
    have hnot : w ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
      intro hs
      have hn : ‖w‖ = 1 := by simpa only [abs_one, mem_sphere, dist_zero_right] using hs
      have hl : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
      linarith
    have hz := Complex.hasDerivAt_circleIntegral_sub_inv_smul hci hnot
    exact ((hz.const_mul (2*(2*Real.pi*Complex.I : ℂ)⁻¹)).sub_const
      (Real.circleAverage (fun ζ => (φ ζ : ℂ)) 0 1)).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball

theorem complexPoissonCauchyExtension_re_harmonicOnNhd
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (sphere (0 : ℂ) 1)) :
    InnerProductSpace.HarmonicOnNhd
      (fun w => (complexPoissonCauchyExtension φ w).re) (ball (0 : ℂ) 1) := by
  intro w hw
  exact (complexPoissonCauchyExtension_analyticOnNhd φ hφ w hw).harmonicAt_re


/-- The real Poisson integral of the actual boundary datum. -/
noncomputable def realPoissonBoundaryExtension (φ : ℂ → ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 w ζ * φ ζ) 0 1

/-- Exact normalization of the Herglotz average as a Cauchy construction. -/
theorem circleAverage_herglotz_eq_complexPoissonCauchyExtension
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (sphere (0 : ℂ) 1))
    {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage (fun ζ => herglotzRieszKernel 0 w ζ • (φ ζ : ℂ)) 0 1 =
      complexPoissonCauchyExtension φ w := by
  let S : Set ℂ := sphere 0 1
  let f : ℂ → ℂ := fun ζ => (φ ζ : ℂ)
  let A : ℂ → ℂ := fun ζ => (ζ-w)⁻¹ • f ζ
  let B : ℂ → ℂ := fun ζ => ζ⁻¹ • f ζ
  have hz0 {ζ : ℂ} (hζ : ζ ∈ S) : ζ ≠ 0 := by
    have hn : ‖ζ‖ = 1 := by simpa only [S, mem_sphere, dist_zero_right] using hζ
    intro hz
    simpa only [hz, norm_zero, zero_ne_one] using hn
  have hzw {ζ : ℂ} (hζ : ζ ∈ S) : ζ-w ≠ 0 := by
    intro he
    have heq : ζ = w := sub_eq_zero.mp he
    have hn : ‖ζ‖ = 1 := by simpa only [S, mem_sphere, dist_zero_right] using hζ
    rw [heq] at hn
    linarith
  have hf : ContinuousOn f S := Complex.continuous_ofReal.comp_continuousOn hφ
  have hA : ContinuousOn A S :=
    ((continuousOn_id.sub continuousOn_const).inv₀ (fun ζ hζ => hzw hζ)).smul hf
  have hB : ContinuousOn B S :=
    (continuousOn_id.inv₀ (fun ζ hζ => hz0 hζ)).smul hf
  have h2A : CircleIntegrable (fun ζ => (2 : ℂ) • A ζ) 0 1 :=
    (hA.const_smul (2 : ℂ)).circleIntegrable (by norm_num)
  have hBi : CircleIntegrable B 0 1 := hB.circleIntegrable (by norm_num)
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  have heq : (∮ ζ in C(0,1), (ζ-0)⁻¹ •
      (herglotzRieszKernel 0 w ζ • (φ ζ : ℂ))) =
      ∮ ζ in C(0,1), (2 : ℂ) • A ζ-B ζ := by
    apply circleIntegral.integral_congr (by norm_num)
    intro ζ hζ
    have hn0 := hz0 hζ
    have hnw := hzw hζ
    dsimp [A, B, f, herglotzRieszKernel]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hn0, hnw]
    ring
  rw [heq, circleIntegral.integral_sub h2A hBi, circleIntegral.integral_smul]
  unfold complexPoissonCauchyExtension
  rw [Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  simp only [A, B, f, sub_zero, smul_eq_mul]
  ring

/-- The actual integral, rather than a postulated Dirichlet solution,
is the real part of the analytic Cauchy construction. -/
theorem complexPoissonCauchyExtension_re_eq_poisson
    (φ : ℂ → ℝ) (hφ : ContinuousOn φ (sphere (0 : ℂ) 1))
    {w : ℂ} (hw : ‖w‖ < 1) :
    (complexPoissonCauchyExtension φ w).re = realPoissonBoundaryExtension φ w := by
  have hnot : w ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    intro hs
    have hn : ‖w‖ = 1 := by simpa only [abs_one, mem_sphere, dist_zero_right] using hs
    linarith
  rw [← circleAverage_herglotz_eq_complexPoissonCauchyExtension φ hφ hw]
  rw [re_circleAverage_herglotzRieszKernel_smul (hφ.circleIntegrable (by norm_num)) hnot]
  unfold realPoissonBoundaryExtension
  apply congrArg (fun f : ℂ → ℝ => Real.circleAverage f 0 1)
  funext ζ
  simp only [Pi.smul_apply, Pi.mul_apply, Function.comp_def, smul_eq_mul,
    poissonKernel_eq_re_herglotzRieszKernel]

end SpringerLean

#print axioms SpringerLean.complexPoissonCauchyExtension_analyticOnNhd
#print axioms SpringerLean.complexPoissonCauchyExtension_re_harmonicOnNhd

#print axioms SpringerLean.circleAverage_herglotz_eq_complexPoissonCauchyExtension
#print axioms SpringerLean.complexPoissonCauchyExtension_re_eq_poisson
