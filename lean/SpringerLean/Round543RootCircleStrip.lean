import SpringerLean.Round498ExteriorCircleSupport
import SpringerLean.Round486StripConvexity

namespace SpringerLean
set_option Elab.async false

/-- The geometric strip step, with the actual maximum root width on a source
circle. The explicit coefficient/logarithm bound on that width is separate. -/
theorem exteriorOmitted_exists_circle_strip
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (R : ℝ)
    (hP : (R : ℂ) ∈ exteriorOmitted F) {r : ℝ} (hr : 1 < r) :
    ∃ (H : ℂ → ℂ) (t : ℂ), CenteredExteriorUnivalent H ∧
      (∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - (R : ℂ)) ∧
      ‖t‖ = r ∧
      (∀ z : ℂ, ‖z‖ = r → |(H z).re| ≤ |(H t).re|) ∧
      ∀ w ∈ convexHull ℝ (exteriorOmitted F),
        w.im ^ 2 ≤ 4 * (H t).re ^ 2 * ((H t).re ^ 2 + R - w.re) ∧
        ‖w‖ ^ 2 ≤ (w.re - 2 * (H t).re ^ 2) ^ 2 + 4 * (H t).re ^ 2 * R := by
  obtain ⟨H, hH, ho, hb, hsquare, hK⟩ :=
    exteriorOmitted_exists_root_with_omitted_set F hc hP
  have hSE : Metric.sphere (0 : ℂ) r ⊆ exteriorDisk := by
    intro z hz
    have hzr : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
    change 1 < ‖z‖
    rwa [hzr]
  have hcont : ContinuousOn (fun z : ℂ => |(H z).re|) (Metric.sphere (0 : ℂ) r) :=
    (Complex.continuous_re.comp_continuousOn (hH.1.continuousOn.mono hSE)).abs
  have hnonempty : (Metric.sphere (0 : ℂ) r).Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r)]
  obtain ⟨t, ht, hmax⟩ := (isCompact_sphere (0 : ℂ) r).exists_isMaxOn hnonempty hcont
  have htNorm : ‖t‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right] using ht
  let M : ℝ := |(H t).re|
  have hM : 0 ≤ M := abs_nonneg _
  have hbound : ∀ u ∈ exteriorOmitted H, |u.re| ≤ M := by
    intro u hu
    obtain ⟨z, hz, hpos⟩ := exteriorOmitted_projection_circle_witness H hH hr 1 hu
    obtain ⟨v, hv, hneg⟩ := exteriorOmitted_projection_circle_witness H hH hr (-1) hu
    simp only [one_mul] at hpos
    simp only [neg_one_mul, Complex.neg_re] at hneg
    have hzp : |(H z).re| ≤ M := hmax (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)
    have hvp : |(H v).re| ≤ M := hmax (by simpa only [Metric.mem_sphere, dist_zero_right] using hv)
    apply abs_le.mpr
    constructor
    · linarith [neg_le_abs (H v).re]
    · exact hpos.trans ((le_abs_self _).trans hzp)
  have hroot : ∀ w ∈ exteriorOmitted F,
      ∃ v : ℂ, v ^ 2 = w - (R : ℂ) ∧ v.re ^ 2 ≤ M ^ 2 := by
    intro w hw
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (w - (R : ℂ)) (by norm_num : 0 < (2 : ℕ))
    have hvK : v ∈ exteriorOmitted H := (hK v).mpr (by simpa [hv] using hw)
    have hvb := hbound v hvK
    refine ⟨v, hv, ?_⟩
    have hh := (sq_le_sq₀ (abs_nonneg v.re) hM).mpr hvb
    simpa only [sq_abs] using hh
  have hhull := convexHull_subset_parabolicStrip_of_root_bound
    (exteriorOmitted F) (sq_nonneg M) hroot
  refine ⟨H, t, hH, hsquare, htNorm, ?_, ?_⟩
  · intro z hz
    exact hmax (by simpa only [Metric.mem_sphere, dist_zero_right] using hz)
  · intro w hw
    have hs : w.im ^ 2 ≤ 4 * M ^ 2 * (M ^ 2 + R - w.re) := hhull hw
    have hMsq : M ^ 2 = (H t).re ^ 2 := sq_abs _
    rw [hMsq] at hs
    refine ⟨hs, ?_⟩
    have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      simpa [Complex.normSq_apply, pow_two] using Complex.sq_norm w
    nlinarith

end SpringerLean
