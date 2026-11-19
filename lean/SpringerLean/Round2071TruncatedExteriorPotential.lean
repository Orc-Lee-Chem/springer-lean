import SpringerLean.Round2070SmoothExteriorBoundaryLaw
import SpringerLean.Round480OmittedRadius

open MeasureTheory Set Real Filter Metric
open scoped Topology

namespace SpringerLean

/-- A continuous logarithmic kernel with finite cutoffs at both ends.
On the diagonal it takes the lower cutoff value `log ε`. -/
noncomputable def clippedLogDistance (x : ℂ) (ε R : ℝ)
    (hε : 0 < ε) (hεR : ε ≤ R) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => Real.log (min R (max ε ‖z - x‖)), by
      apply (continuous_const.min (continuous_const.max (continuous_id.sub continuous_const).norm)).log
      intro z
      exact ne_of_gt (lt_min (hε.trans_le hεR) (hε.trans_le (le_max_left _ _)))⟩
    (Real.log R - Real.log ε) (by
      intro z w
      have bounds (y : ℂ) : Real.log ε ≤ Real.log (min R (max ε ‖y-x‖)) ∧
          Real.log (min R (max ε ‖y-x‖)) ≤ Real.log R :=
        ⟨Real.log_le_log hε (le_min hεR (le_max_left _ _)),
          Real.log_le_log (hε.trans_le (le_min hεR (le_max_left _ _))) (min_le_left _ _)⟩
      change |Real.log (min R (max ε ‖z-x‖)) - Real.log (min R (max ε ‖w-x‖))| ≤ _
      rw [abs_le]
      constructor <;> linarith [(bounds z).1, (bounds z).2, (bounds w).1, (bounds w).2])

@[simp] theorem clippedLogDistance_apply (x z : ℂ) (ε R : ℝ)
    (hε : 0 < ε) (hεR : ε ≤ R) :
    clippedLogDistance x ε R hε hεR z = Real.log (min R (max ε ‖z-x‖)) := rfl

/-- The lower-truncated logarithmic potential of the actual radial law
is nonnegative at every point of the omitted set. The upper cutoff
`5` is inactive on the relevant supports. -/
theorem actualExteriorBoundaryProbability_clippedLog_nonneg
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (x : ℂ) (hx : x ∈ exteriorOmitted F)
    (ε : ℝ) (hε : 0 < ε) (hε5 : ε ≤ 5) :
    0 ≤ ∫ z, clippedLogDistance x ε 5 hε hε5 z ∂actualExteriorBoundaryProbability F := by
  let φ := clippedLogDistance x ε 5 hε hε5
  have hlim := smoothExteriorBoundaryProbability_boundedTest_tendsto F hF φ
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with s hs
  have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 1 / 2).trans hs.1
  have hsR : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs.2
  have hx2 := exteriorOmitted_norm_le_two F hF hx
  have hsub : sphere (0 : ℂ) s⁻¹ ⊆ exteriorDisk := by
    intro z hz
    have hz' : ‖z‖ = s⁻¹ := by simpa [mem_sphere, dist_zero_right] using hz
    change 1 < ‖z‖
    rwa [hz']
  have hnz (z : ℂ) (hz : z ∈ sphere 0 s⁻¹) : ‖F z - x‖ ≠ 0 := by
    intro heq
    exact hx ⟨z, hsub hz, sub_eq_zero.mp (norm_eq_zero.mp heq)⟩
  have hFc := hF.1.continuousOn.mono hsub
  have hlogc : ContinuousOn (fun z => Real.log ‖F z - x‖) (sphere 0 s⁻¹) :=
    ((hFc.sub continuousOn_const).norm).log hnz
  have hφc : ContinuousOn (fun z => φ (F z)) (sphere 0 s⁻¹) :=
    φ.continuous.comp_continuousOn hFc
  have hle (z : ℂ) (hz : z ∈ sphere 0 s⁻¹) :
      Real.log ‖F z - x‖ ≤ φ (F z) := by
    have hz' : ‖z‖ = s⁻¹ := by simpa [mem_sphere, dist_zero_right] using hz
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, z = Complex.polarCoord.symm (s⁻¹, θ) := by
      refine ⟨z.arg, ?_⟩
      rw [← hz', Complex.polarCoord_symm_apply]
      simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin] using
        (Complex.norm_mul_cos_add_sin_mul_I z).symm
    have hi : s⁻¹ ≤ 2 := by
      calc
        s⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hs.1.le
        _ = 2 := by norm_num
    have hdist : ‖F z - x‖ ≤ 5 := (norm_sub_le _ _).trans (by
      rw [hθ]
      linarith [exterior_polar_norm_le_radius_add_inv F hF hs0 hs.2 θ, hs.2])
    exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm (hnz z hz)))
      (le_min hdist (le_max_right _ _))
  rw [smoothExteriorBoundaryProbability_integral_eq_circleAverage F hF s hs0 hs.2
    φ φ.continuous.measurable]
  have hcomp := Real.circleAverage_mono (hlogc.circleIntegrable (inv_pos.mpr hs0).le)
    (hφc.circleIntegrable (inv_pos.mpr hs0).le)
    (by simpa [abs_of_pos (inv_pos.mpr hs0)] using hle)
  rw [exterior_circle_log_potential_of_omitted F hF x hx s hs0 hs.2] at hcomp
  exact (neg_nonneg.mpr (Real.log_nonpos hs0.le hs.2.le)).trans hcomp

end SpringerLean
