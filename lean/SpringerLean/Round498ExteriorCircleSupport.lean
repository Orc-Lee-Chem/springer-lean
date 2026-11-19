import SpringerLean.Round494ExteriorClosedImage
import SpringerLean.Round12Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set
open scoped Topology

namespace SpringerLean
set_option Elab.async false

theorem exteriorOmittedAbove_frontier_subset_circle_image
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {r : ℝ} (hr : 1 < r) :
    frontier (F '' exteriorAbove r)ᶜ ⊆ F '' Metric.sphere (0 : ℂ) r := by
  let S : Set ℂ := {z | r ≤ ‖z‖}
  have hclosed := exterior_closed_image_isClosed F hc hr
  have hsub : F '' exteriorAbove r ⊆ F '' S := by
    rintro w ⟨z, hz, rfl⟩
    refine ⟨z, ?_, rfl⟩
    change r ≤ ‖z‖
    exact le_of_lt hz
  have hcl : closure (F '' exteriorAbove r) ⊆ F '' S := closure_minimal hsub hclosed
  have hEsub : exteriorAbove r ⊆ exteriorDisk := fun z hz => lt_trans hr hz
  have hopen : IsOpen (F '' exteriorAbove r) := exterior_image_open_of_isOpen F hc
    (isOpen_lt continuous_const continuous_norm) hEsub
  intro w hw
  have hwim : w ∈ F '' S := by
    apply hcl
    rw [frontier_compl] at hw
    exact frontier_subset_closure hw
  have hwK : w ∈ (F '' exteriorAbove r)ᶜ := by
    have hh := frontier_subset_closure hw
    rwa [hopen.isClosed_compl.closure_eq] at hh
  obtain ⟨z, hz, hzF⟩ := hwim
  have hle : ‖z‖ ≤ r := by
    by_contra hn
    exact hwK ⟨z, lt_of_not_ge hn, hzF⟩
  exact ⟨z, by simpa only [Metric.mem_sphere, dist_zero_right] using le_antisymm hle hz, hzF⟩

theorem exteriorOmittedAbove_projection_circle_witness
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {r : ℝ} (hr : 1 < r)
    (c : ℂ) {w : ℂ} (hw : w ∈ (F '' exteriorAbove r)ᶜ) :
    ∃ z : ℂ, ‖z‖ = r ∧ (c * w).re ≤ (c * F z).re := by
  by_cases hc0 : c = 0
  · refine ⟨(r : ℂ), ?_, by simp [hc0]⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r)]
  let K : Set ℂ := (F '' exteriorAbove r)ᶜ
  have hK : IsCompact K := by
    have hi0 : 0 < r⁻¹ := inv_pos.mpr (by linarith)
    have hi1 : r⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < r)).mpr hr
    simpa only [exteriorOmittedAtScale, inv_inv] using
      exteriorOmittedAtScale_isCompact F hc hi0 hi1
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn ⟨w, hw⟩
    (show Continuous (fun z : ℂ => (c * z).re) by fun_prop).continuousOn
  have hpfront : p ∈ frontier K := by
    by_contra hn
    have hpint : p ∈ interior K := by
      by_contra hi
      apply hn
      change p ∈ closure K \ interior K
      exact ⟨subset_closure hp, hi⟩
    let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ c)
    have hl : IsLocalMax L p := by
      filter_upwards [mem_interior_iff_mem_nhds.mp hpint] with z hz
      exact hmax hz
    have hzero : L = 0 := by
      have h := hl.fderiv_eq_zero
      rwa [L.hasFDerivAt.fderiv] at h
    have h1 := congrArg (fun T : ℂ →L[ℝ] ℝ => T 1) hzero
    have hI := congrArg (fun T : ℂ →L[ℝ] ℝ => T Complex.I) hzero
    simp [L, Complex.mul_re] at h1 hI
    apply hc0
    apply Complex.ext h1
    simpa using hI
  obtain ⟨z, hz, hzp⟩ := exteriorOmittedAbove_frontier_subset_circle_image F hc hr hpfront
  refine ⟨z, by simpa only [Metric.mem_sphere, dist_zero_right] using hz, ?_⟩
  rw [hzp]
  exact hmax hw

theorem exteriorOmitted_projection_circle_witness
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) {r : ℝ} (hr : 1 < r)
    (c : ℂ) {w : ℂ} (hw : w ∈ exteriorOmitted F) :
    ∃ z : ℂ, ‖z‖ = r ∧ (c * w).re ≤ (c * F z).re := by
  apply exteriorOmittedAbove_projection_circle_witness F hc hr c
  rintro ⟨z, hz, hF⟩
  exact hw ⟨z, lt_trans hr hz, hF⟩

end SpringerLean
