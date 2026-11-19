import SpringerLean.Round2095ExteriorGreenRegularity
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

open Set Filter Real Metric MeasureTheory
open scoped Topology

namespace SpringerLean

theorem exteriorGreenCoordinate_pos_iff (F : ℂ → ℂ) (z : ℂ) :
    0 < exteriorGreenCoordinate F z ↔ z ∈ F '' exteriorDisk := by
  classical
  by_cases hz : z ∈ F '' exteriorDisk
  · have hnorm : 1 < ‖exteriorInverse F z‖ := Function.invFunOn_mem hz
    simp [exteriorGreenCoordinate,hz,Real.log_pos hnorm]
  · simp [exteriorGreenCoordinate,hz]

theorem exteriorGreenCoordinate_neg_of_odd
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (z : ℂ) :
    exteriorGreenCoordinate F (-z) = exteriorGreenCoordinate F z := by
  classical
  have hzneg (w : ℂ) (hw : w ∈ exteriorDisk) : -w ∈ exteriorDisk := by
    change 1 < ‖-w‖
    simpa only [norm_neg] using (show 1 < ‖w‖ from hw)
  have hfor (w : ℂ) (hw : w ∈ F '' exteriorDisk) : -w ∈ F '' exteriorDisk := by
    obtain ⟨t,ht,rfl⟩ := hw
    exact ⟨-t,hzneg t ht,ho t ht⟩
  by_cases hz : z ∈ F '' exteriorDisk
  · have hn := hfor z hz
    have hInv (w : ℂ) (hw : w ∈ exteriorDisk) : exteriorInverse F (F w) = w :=
      hF.2.1.leftInvOn_invFunOn hw
    obtain ⟨t,ht,htv⟩ := hz
    rw [exteriorGreenCoordinate, if_pos hn, exteriorGreenCoordinate, if_pos ⟨t,ht,htv⟩]
    rw [←htv, ←ho t ht, hInv (-t) (hzneg t ht), hInv t ht, norm_neg]
  · have hneg : -z ∉ F '' exteriorDisk := fun h => hz (by simpa only [neg_neg] using hfor (-z) h)
    simp [exteriorGreenCoordinate,hz,hneg]

theorem zero_mem_exteriorOmitted_of_odd
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) : (0:ℂ) ∈ exteriorOmitted F := by
  rintro ⟨z,hz,he⟩
  have hm : -z ∈ exteriorDisk := by
    change 1 < ‖-z‖
    simpa only [norm_neg] using (show 1 < ‖z‖ from hz)
  have e : -z = z := hF.2.1 hm hz (by rw [ho z hz,he,neg_zero])
  exact exterior_ne_zero hz (by linear_combination -e/2)

private theorem Complex_analyticAt_real_log_norm_comp
    (g : ℝ → ℂ) (θ : ℝ) (hg : AnalyticAt ℝ g θ) (hne : g θ ≠ 0) :
    AnalyticAt ℝ (fun t => Real.log ‖g t‖) θ := by
  let f (t : ℝ) := g t / g θ
  have hf : AnalyticAt ℝ f θ := by unfold f; exact hg.div analyticAt_const hne
  have hf1 : f θ = 1 := div_self hne
  have hLog : AnalyticAt ℝ Complex.log (f θ) := by
    rw [hf1]
    exact (analyticAt_clog (by simp [Complex.slitPlane])).restrictScalars
  have ha : AnalyticAt ℝ (fun t => (Complex.log (f t)).re + Real.log ‖g θ‖) θ :=
    ((Complex.reCLM.analyticAt _).comp (hLog.comp hf)).add analyticAt_const
  have hEq : (fun t => (Complex.log (f t)).re + Real.log ‖g θ‖) =ᶠ[𝓝 θ]
      fun t => Real.log ‖g t‖ := by
    have ht : ∀ᶠ t in 𝓝 θ, g t ≠ 0 := hg.continuousAt.eventually_ne hne
    filter_upwards [ht] with t ht
    rw [Complex.log_re, show ‖f t‖ = ‖g t‖/‖g θ‖ by exact norm_div _ _,
      Real.log_div (norm_ne_zero_iff.mpr ht) (norm_ne_zero_iff.mpr hne)]
    ring
  exact ha.congr hEq

/-- Positive angular levels of the actual Green coordinate are locally
real analytic in the angle. The hypothesis is precisely that the point
lies in the exterior image. -/
theorem exteriorGreenCoordinate_angular_analyticAt
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (r θ : ℝ)
    (hθ : circleMap 0 r θ ∈ F '' exteriorDisk) :
    AnalyticAt ℝ (fun t => exteriorGreenCoordinate F (circleMap 0 r t)) θ := by
  classical
  let w (t : ℝ) := circleMap 0 r t
  have hw : AnalyticAt ℝ w θ := by
    have hl : AnalyticAt ℝ (fun t : ℝ => (t:ℂ)*Complex.I) θ :=
      (Complex.ofRealCLM.analyticAt θ).mul analyticAt_const
    have he : AnalyticAt ℝ Complex.exp ((θ:ℂ)*Complex.I) := analyticAt_cexp.restrictScalars
    have hs : AnalyticAt ℝ (fun t : ℝ => (r:ℂ)*Complex.exp ((t:ℂ)*Complex.I)) θ :=
      analyticAt_const.mul (he.comp (f := fun t : ℝ => (t:ℂ)*Complex.I) (x := θ) hl)
    simpa only [w,circleMap_zero] using hs
  have hi : AnalyticAt ℂ (exteriorInverse F) (w θ) := by
    obtain ⟨z,hz,he⟩ := hθ
    change F z = w θ at he
    exact he ▸ exteriorInverse_analyticAt_image F hF z hz
  have hi' : AnalyticAt ℝ (exteriorInverse F) (w θ) := hi.restrictScalars
  have harg := Complex_analyticAt_real_log_norm_comp (exteriorInverse F ∘ w) θ (hi'.comp hw)
    (exterior_ne_zero (Function.invFunOn_mem hθ))
  apply harg.congr
  have hOpen := exterior_image_open_of_isOpen F hF exteriorDisk_isOpen subset_rfl
  have hs : ∀ᶠ t in 𝓝 θ, w t ∈ F '' exteriorDisk :=
    hw.continuousAt.eventually (hOpen.mem_nhds hθ)
  filter_upwards [hs] with t ht
  simp only [Function.comp_apply, exteriorGreenCoordinate, if_pos ht, w]

end SpringerLean
