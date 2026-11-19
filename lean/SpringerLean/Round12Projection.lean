import SpringerLean.Round12Compact
import Mathlib.Analysis.Complex.AbsMax

open Filter
open scoped Topology ComplexConjugate

namespace SpringerLean

/-- Maximum principle for the real part of the analytic projection of the
regularized harmonic filling. The boundary point is an actual unit complex
number; no boundary extension of the original map is assumed. -/
theorem regular_projection_boundary_max
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (c * regularHarmonic s F z).re ≤
        (c * regularHarmonic s F ζ).re := by
  let J : ℂ → ℂ := fun u => conj c * u + c * regularForwardGerm s F u
  let E : ℂ → ℂ := fun u => Complex.exp (J u)
  have hInv : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hClosedSub : Metric.closedBall (0 : ℂ) 1 ⊆
      Metric.ball (0 : ℂ) s⁻¹ :=
    Metric.closedBall_subset_ball hInv
  have hOpenSub : Metric.ball (0 : ℂ) 1 ⊆
      Metric.ball (0 : ℂ) s⁻¹ :=
    Metric.ball_subset_ball hInv.le
  have hJ : AnalyticOnNhd ℂ J (Metric.ball (0 : ℂ) s⁻¹) := by
    intro u hu
    have hg := regularForwardGerm_analyticOnNhd F hc hs0 u hu
    dsimp only [J]
    fun_prop
  have hE : AnalyticOnNhd ℂ E (Metric.ball (0 : ℂ) s⁻¹) := by
    intro u hu
    have hJu := hJ u hu
    dsimp only [E]
    fun_prop
  have hDiff : DiffContOnCl ℂ E (Metric.ball (0 : ℂ) 1) := by
    constructor
    · exact (hE.mono hOpenSub).differentiableOn
    · exact hE.continuousOn.mono
        (Metric.closure_ball_subset_closedBall.trans hClosedSub)
  obtain ⟨u, huFront, huMax⟩ :=
    Complex.exists_mem_frontier_isMaxOn_norm
      (Metric.isBounded_ball : Bornology.IsBounded (Metric.ball (0 : ℂ) 1))
      ⟨0, Metric.mem_ball_self (by norm_num)⟩ hDiff
  have huNorm : ‖u‖ = 1 := by
    have huSphere := Metric.frontier_ball_subset_sphere huFront
    simpa only [Metric.mem_sphere, dist_zero_right] using huSphere
  have hzClosed : conj z ∈ closure (Metric.ball (0 : ℂ) 1) := by
    apply subset_closure
    simpa only [Metric.mem_ball, dist_zero_right,
      Complex.norm_conj] using hz
  have hMax : ‖E (conj z)‖ ≤ ‖E u‖ := huMax hzClosed
  have hRe : (J (conj z)).re ≤ (J u).re := by
    dsimp only [E] at hMax
    rw [Complex.norm_exp, Complex.norm_exp] at hMax
    exact (Real.exp_le_exp).mp hMax
  let ζ : ℂ := conj u
  refine ⟨ζ, by simpa only [ζ, Complex.norm_conj] using huNorm, ?_⟩
  have hJ_eq (v : ℂ) :
      (J v).re = (c * regularHarmonic s F (conj v)).re := by
    dsimp [J, regularHarmonic]
    simp only [Complex.conj_conj, mul_add, Complex.add_re]
    simp [Complex.mul_re]
  simpa only [hJ_eq, ζ, Complex.conj_conj] using hRe

/-- For every real direction, the regularized filling is bounded by a
point of the genuine unscaled omitted set `K_s`. -/
theorem regular_projection_omittedAtScale_witness
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ w ∈ exteriorOmittedAtScale F s,
      (c * regularHarmonic s F z).re ≤
        s * (c * w).re := by
  obtain ⟨ζ, hζ, hmax⟩ :=
    regular_projection_boundary_max F hc hs0 hs1 c hz
  let w : ℂ := F (ζ / (s : ℂ))
  have hInv : 1 < s⁻¹ := (one_lt_inv_iff₀).mpr ⟨hs0, hs1⟩
  have hζnorm : ‖ζ / (s : ℂ)‖ = s⁻¹ := by
    rw [norm_div, hζ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs0]
    simp
  have hζext : ζ / (s : ℂ) ∈ exteriorDisk := by
    change 1 < ‖ζ / (s : ℂ)‖
    rw [hζnorm]
    exact hInv
  have hw : w ∈ exteriorOmittedAtScale F s := by
    intro hmem
    obtain ⟨v, hv, hvF⟩ := hmem
    have hvExt : v ∈ exteriorDisk := by
      change 1 < ‖v‖
      exact hInv.trans hv
    have hEq : v = ζ / (s : ℂ) :=
      hc.2.1 hvExt hζext hvF
    change s⁻¹ < ‖v‖ at hv
    have hlt : s⁻¹ < s⁻¹ := by
      simpa only [hEq, hζnorm] using hv
    exact (lt_irrefl _) hlt
  refine ⟨w, hw, ?_⟩
  rw [regularHarmonic_unitCircle_eq_actual F hs0 hζ] at hmax
  have hRe : (c * rescaleExterior s F ζ).re = s * (c * w).re := by
    dsimp only [rescaleExterior, w]
    have heq : c * ((s : ℂ) * F (ζ / (s : ℂ))) =
        (s : ℂ) * (c * F (ζ / (s : ℂ))) := by ring
    rw [heq, Complex.mul_re]
    simp
  exact hmax.trans_eq hRe

end SpringerLean
