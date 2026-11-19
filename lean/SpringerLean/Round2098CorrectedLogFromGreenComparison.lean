import SpringerLean.Round2096GreenRadialHinge
import SpringerLean.Round2097ProbabilityHingeComparison
import SpringerLean.Round2040EvenBLPTangentExtension
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter Real
open scoped Topology

namespace SpringerLean

/-- The bounded radial form of the corrected logarithmic test. -/
noncomputable def evenStarCorrectedRadialTest (k : ℕ) (r : ℝ) : ℝ :=
  log (1+(|r|/2)^(1/(k:ℝ))) - r^2/(64*(k:ℝ)^2)

theorem evenStarCorrectedRadialTest_eq_log (k : ℕ) {r : ℝ} (hr : 0 < r) :
    evenStarCorrectedRadialTest k r = evenStarBLPCorrectedLog k (log r) := by
  have h₁ : (r/2)^(1/(k:ℝ)) = exp ((log r-log 2)/(k:ℝ)) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_div hr.ne' (by norm_num)]
    congr 1
    ring
  have h₂ : exp (2*log r) = r^2 := by
    rw [show 2*log r = log r+log r by ring, Real.exp_add, Real.exp_log hr, pow_two]
  simp only [evenStarCorrectedRadialTest, evenStarBLPCorrectedLog, abs_of_pos hr, h₁, h₂]

theorem evenStarCorrectedRadialTest_continuous (k : ℕ) :
    Continuous (evenStarCorrectedRadialTest k) := by
  unfold evenStarCorrectedRadialTest
  have hP : Continuous (fun r : ℝ => (|r|/2)^(1/(k:ℝ))) :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ 1/(k:ℝ))).comp (by fun_prop)
  apply ((continuous_const.add hP).log _).sub (by fun_prop)
  intro r
  exact (show 0 < 1+(|r|/2)^(1/(k:ℝ)) by positivity).ne'

private theorem evenStarBLPCorrectedLog_continuous (k : ℕ) (hk : 0 < k) :
    Continuous (evenStarBLPCorrectedLog k) :=
  continuous_iff_continuousAt.mpr fun x =>
    (evenStarBLPCorrectedLog_hasDerivAt k hk x).continuousAt

theorem evenStarBLPCorrectedLog_monotoneOn (k : ℕ) (hk : 0 < k) :
    MonotoneOn (evenStarBLPCorrectedLog k) (Iic (log 2)) := by
  have hC := evenStarBLPCorrectedLog_continuous k hk
  apply monotoneOn_of_deriv_nonneg (convex_Iic _) hC.continuousOn
  · exact fun x _ => (evenStarBLPCorrectedLog_hasDerivAt k hk x).differentiableAt.differentiableWithinAt
  intro x hx
  have hx' : x ∈ Iic (log 2) := interior_subset hx
  let y := exp ((x-log 2)/(k:ℝ))
  have hy : 0 < y := exp_pos _
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 1 ≤ (k:ℝ)*(1+y) := by nlinarith
  have h2 := div_le_div_of_nonneg_left hy.le (by positivity : 0 < (k:ℝ)*(1+y))
    (show (k:ℝ)*(1+y) ≤ (k:ℝ)^2*(1+y)^2 by nlinarith [sq_nonneg ((k:ℝ)*(1+y)-1)])
  have hcurv := evenStar_log_kernel_curvature_actual_x k hk x hx'
  change exp (2*x)/(16*(k:ℝ)^2) ≤ y/((k:ℝ)^2*(1+y)^2) at hcurv
  have hhalf : exp (2*x)/(32*(k:ℝ)^2) ≤ exp (2*x)/(16*(k:ℝ)^2) := by gcongr <;> norm_num
  rw [(evenStarBLPCorrectedLog_hasDerivAt k hk x).deriv]
  exact sub_nonneg.mpr (hhalf.trans (hcurv.trans h2))

private theorem max_log_trunc_sub_eq_posLog {δ r c : ℝ}
    (hδ : 0 < δ) (hr : 0 ≤ r) (hc : log δ ≤ c) :
    max (log (max δ r)-c) 0 = posLog ((exp c)⁻¹*r) := by
  by_cases hr0 : r = 0
  · rw [hr0,max_eq_left hδ.le,mul_zero,posLog_zero,max_eq_right (sub_nonpos.mpr hc)]
  have hre : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [posLog_apply, Real.log_mul (inv_ne_zero (exp_pos _).ne') hr0, Real.log_inv, Real.log_exp]
  rw [show -c + log r = log r-c by ring]
  rcases le_total δ r with h | h
  · rw [max_eq_right h,max_comm]
  · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr hc), max_eq_left]
    exact sub_nonpos.mpr ((Real.log_le_log hre h).trans hc)

/-- Reduction of the corrected radial test to a genuine Green circular
mean comparison. This statement isolates the remaining symmetrization
input, which is still an explicit assumption. -/
theorem evenStarCorrectedRadialTest_integral_le_of_green_comparison
    (F G : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hG : CenteredExteriorUnivalent G)
    (k : ℕ) (hk : 0 < k)
    (hcomp : ∀ r > 0, circleAverage (exteriorGreenCoordinate F) 0 r ≤
      circleAverage (exteriorGreenCoordinate G) 0 r) :
    (∫ z, evenStarCorrectedRadialTest k ‖z‖ ∂actualExteriorBoundaryProbability F) ≤
      ∫ z, evenStarCorrectedRadialTest k ‖z‖ ∂actualExteriorBoundaryProbability G := by
  let μ := actualExteriorBoundaryProbability F
  let ν := actualExteriorBoundaryProbability G
  let ψ := evenStarBLPCorrectedLog k
  let H := evenStarCorrectedRadialTest k
  have hμ : IsProbabilityMeasure μ := ⟨actualExteriorBoundaryProbability_univ F hF⟩
  have hν : IsProbabilityMeasure ν := ⟨actualExteriorBoundaryProbability_univ G hG⟩
  have hnorm (f : ℂ → ℂ) (hf : CenteredExteriorUnivalent f) :
      ∀ᵐ z ∂actualExteriorBoundaryProbability f, ‖z‖ ≤ 2 := by
    have hs : ∀ᵐ z ∂actualExteriorBoundaryProbability f, z ∈ exteriorOmitted f :=
      actualExteriorBoundaryProbability_ae_mem_omitted f hf (exteriorOmitted_isCompact f hf).isClosed
    exact hs.mono (fun _ hz => exteriorOmitted_norm_le_two f hf hz)
  let δ (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδ₂ (n : ℕ) : δ n < 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have htrunc (n : ℕ) : (∫ z, H (max (δ n) ‖z‖) ∂μ) ≤ ∫ z, H (max (δ n) ‖z‖) ∂ν := by
    let V (z : ℂ) := log (max (δ n) ‖z‖)
    have hV : Continuous V := (continuous_const.max continuous_norm).log
      (fun z => (lt_of_lt_of_le (hδ n) (le_max_left _ _)).ne')
    have hVm (f : ℂ → ℂ) (hf : CenteredExteriorUnivalent f) :
        ∀ᵐ z ∂actualExteriorBoundaryProbability f, V z ∈ Icc (log (δ n)) (log 2) := by
      filter_upwards [hnorm f hf] with z hz
      exact ⟨log_le_log (hδ n) (le_max_left _ _),
        log_le_log ((hδ n).trans_le (le_max_left _ _)) (max_le (hδ₂ n).le hz)⟩
    have hc : ConvexOn ℝ (Icc (log (δ n)) (log 2)) ψ :=
      (evenStarBLPCorrectedLog_convexOn_support k hk).subset
        (fun _ hz => hz.2) (convex_Icc _ _)
    have hm : MonotoneOn ψ (Icc (log (δ n)) (log 2)) :=
      (evenStarBLPCorrectedLog_monotoneOn k hk).mono (fun _ hz => hz.2)
    have hh (c : ℝ) (hc : c ∈ Icc (log (δ n)) (log 2)) :
        (∫ z, max (V z-c) 0 ∂μ) ≤ ∫ z, max (V z-c) 0 ∂ν := by
      have he (z : ℂ) : max (V z-c) 0 = posLog ((exp c)⁻¹*‖z‖) :=
        max_log_trunc_sub_eq_posLog (hδ n) (norm_nonneg z) hc.1
      simp_rw [he]
      have h := hcomp (exp c) (exp_pos _)
      rw [exteriorGreenCoordinate_circleAverage_eq_radial_hinge F hF _ (exp_pos _),
        exteriorGreenCoordinate_circleAverage_eq_radial_hinge G hG _ (exp_pos _)] at h
      exact le_of_add_le_add_left h
    have h := integral_mono_convex_of_hinges_on_Icc μ ν V V
      hV.measurable.aemeasurable hV.measurable.aemeasurable (log (δ n)) (log 2)
      (log_lt_log (hδ n) (hδ₂ n)) (hVm F hF) (hVm G hG) hh ψ
      (evenStarBLPCorrectedLog_continuous k hk) hc hm
    have he (z : ℂ) : H (max (δ n) ‖z‖) = ψ (V z) :=
      evenStarCorrectedRadialTest_eq_log k ((hδ n).trans_le (le_max_left _ _))
    simpa only [he] using h
  have hlim (f : ℂ → ℂ) (hf : CenteredExteriorUnivalent f) :
      Tendsto (fun n => ∫ z, H (max (δ n) ‖z‖) ∂actualExteriorBoundaryProbability f)
        atTop (𝓝 (∫ z, H ‖z‖ ∂actualExteriorBoundaryProbability f)) := by
    let ρ := actualExteriorBoundaryProbability f
    have hρ : IsProbabilityMeasure ρ := ⟨actualExteriorBoundaryProbability_univ f hf⟩
    have hcont : Continuous H := evenStarCorrectedRadialTest_continuous k
    obtain ⟨C,hC⟩ := (isCompact_Icc.image hcont : IsCompact (H '' Icc (0:ℝ) 2)).isBounded.exists_norm_le
    apply tendsto_integral_of_dominated_convergence (fun _ : ℂ => C)
    · exact fun n => (hcont.comp (continuous_const.max continuous_norm)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [hnorm f hf] with z hz
      exact hC _ ⟨max (δ n) ‖z‖,⟨(norm_nonneg z).trans (le_max_right _ _),
        max_le (hδ₂ n).le hz⟩,rfl⟩
    · exact .of_forall (fun z => hcont.continuousAt.tendsto.comp (by
        have h := (show Tendsto δ atTop (𝓝 (0:ℝ)) from tendsto_one_div_add_atTop_nhds_zero_nat).max
          (tendsto_const_nhds (x := ‖z‖))
        simpa only [max_eq_right (norm_nonneg z)] using h))
  exact le_of_tendsto_of_tendsto' (hlim F hF) (hlim G hG) htrunc

end SpringerLean
