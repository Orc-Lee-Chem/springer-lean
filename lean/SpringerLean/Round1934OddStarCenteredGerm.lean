import SpringerLean.Round1933OddStarRotation
import Mathlib.Analysis.Complex.RemovableSingularity

open scoped Topology

namespace SpringerLean

private theorem complex_npowRec_eq_pow (n : ℕ) (z : ℂ) :
    npowRec n z = z ^ n := by
  induction n with
  | zero => simp [npowRec]
  | succ n ih => simp [npowRec, pow_succ, ih, mul_comm]

noncomputable def oddStarPerturbationGerm
    (m : ℕ) (t : ℝ) (u : ℂ) : ℂ :=
  (oddStarSeedRootReciprocal m t (u ^ m) - 1) / u

theorem oddStarPerturbation_forwardGerm_eq
    (m : ℕ) (t : ℝ) :
    exteriorForwardGerm (oddStarPerturbation m t) =
      oddStarPerturbationGerm m t := by
  funext u
  by_cases hu : u = 0
  · subst u
    simp [exteriorForwardGerm, oddStarPerturbationGerm]
  · unfold exteriorForwardGerm oddStarPerturbationGerm
    simp only [if_neg hu]
    unfold oddStarPerturbation
    have hpow : ((u⁻¹) ^ m)⁻¹ = u ^ m := by
      rw [inv_pow, inv_inv]
    rw [hpow]
    field_simp [hu]

/-- The reciprocal root has zero first derivative after composition
with the m-th power, for m at least two. -/
theorem oddStarPerturbation_rootComp_hasDerivAt_zero
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    HasDerivAt (fun u : ℂ =>
      oddStarSeedRootReciprocal m t (u ^ m)) 0 0 := by
  have hroot := oddStarSeedRootReciprocal_analyticOnNhd_unitDisk m t ht
  have hrootAt : DifferentiableAt ℂ (oddStarSeedRootReciprocal m t) 0 :=
    (hroot 0 (by simp)).differentiableAt
  have hm1 : m - 1 ≠ 0 := by omega
  have hpow : HasDerivAt (fun u : ℂ => u ^ m) 0 0 := by
    simpa [hm1] using hasDerivAt_pow m (0 : ℂ)
  have hrootAt' : HasDerivAt (oddStarSeedRootReciprocal m t)
      (deriv (oddStarSeedRootReciprocal m t) 0) (0 ^ m) := by
    simpa [zero_pow (by omega : m ≠ 0)] using hrootAt.hasDerivAt
  simpa only [Function.comp_def, complex_npowRec_eq_pow, mul_zero] using
    hrootAt'.comp (0 : ℂ) hpow

/-- The apparent pole of the centered Laurent correction at the
reciprocal origin is removable, and the corrected value is zero. -/
theorem oddStarPerturbationGerm_analyticAt_zero
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    AnalyticAt ℂ (oddStarPerturbationGerm m t) 0 := by
  have hderiv := oddStarPerturbation_rootComp_hasDerivAt_zero m hm t ht
  have hzero : oddStarPerturbationGerm m t 0 = 0 := by
    simp [oddStarPerturbationGerm]
  have hlim : Filter.Tendsto (oddStarPerturbationGerm m t)
      (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    have h := hderiv.tendsto_slope_zero
    have heq : oddStarPerturbationGerm m t =
        fun u : ℂ => u⁻¹ *
          (oddStarSeedRootReciprocal m t (u ^ m) - 1) := by
      funext u
      simp [oddStarPerturbationGerm, div_eq_mul_inv, mul_comm]
    rw [heq]
    simpa [zero_pow (by omega : m ≠ 0),
      oddStarSeedRootReciprocal_zero, smul_eq_mul] using h
  have hcont : ContinuousAt (oddStarPerturbationGerm m t) 0 := by
    rw [continuousAt_iff_punctured_nhds, hzero]
    exact hlim
  have hroot := oddStarSeedRootReciprocal_analyticOnNhd_unitDisk m t ht
  have hoff : ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      DifferentiableAt ℂ (oddStarPerturbationGerm m t) u := by
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (by norm_num : (0 : ℝ) < 1)] with u hu hu0
    have hu0' : u ≠ 0 := by simpa using hu0
    have hunorm : ‖u‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    have hpowmem : u ^ m ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [Metric.mem_ball, dist_zero_right]
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg u) hunorm (by omega : m ≠ 0)
    have hrootAt : DifferentiableAt ℂ
        (oddStarSeedRootReciprocal m t) (u ^ m) :=
      (hroot (u ^ m) hpowmem).differentiableAt
    have hcomp : DifferentiableAt ℂ
        (fun v : ℂ => oddStarSeedRootReciprocal m t (v ^ m)) u := by
      have hpowAt : DifferentiableAt ℂ (fun v : ℂ => v ^ m) u := by
        simpa only [complex_npowRec_eq_pow] using
          (hasDerivAt_pow m u).differentiableAt
      exact hrootAt.comp u hpowAt
    have hnum : DifferentiableAt ℂ
        (fun v : ℂ => oddStarSeedRootReciprocal m t (v ^ m) - 1) u :=
      hcomp.sub_const 1
    exact hnum.div differentiableAt_id hu0'
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hoff hcont

theorem oddStarPerturbation_centeredExteriorUnivalent
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    CenteredExteriorUnivalent (oddStarPerturbation m t) := by
  refine ⟨?_, oddStarPerturbation_injOn_exteriorDisk m (by omega) t ht, ?_⟩
  · exact (oddStarPerturbation_analyticOnNhd_exteriorDisk m (by omega) t ht).differentiableOn
  · rw [oddStarPerturbation_forwardGerm_eq]
    exact oddStarPerturbationGerm_analyticAt_zero m hm t ht

end SpringerLean

#print axioms SpringerLean.oddStarPerturbation_forwardGerm_eq
#print axioms SpringerLean.oddStarPerturbation_rootComp_hasDerivAt_zero
#print axioms SpringerLean.oddStarPerturbation_centeredExteriorUnivalent
