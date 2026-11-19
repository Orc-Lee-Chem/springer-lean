import SpringerLean.Round2102GreenAngularLevels
import Mathlib.Topology.MetricSpace.Thickening

open MeasureTheory Set Filter Metric Real
open scoped Topology

namespace SpringerLean

/-- A holomorphic coordinate change preserves harmonicity wherever the
actual Green coordinate is positive. -/
theorem exteriorGreenCoordinate_harmonicOnNhd_comp
    (F φ : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hφ : AnalyticOnNhd ℂ φ univ) :
    InnerProductSpace.HarmonicOnNhd (exteriorGreenCoordinate F ∘ φ)
      (φ ⁻¹' (F '' exteriorDisk)) := by
  classical
  have ho : IsOpen (φ ⁻¹' (F '' exteriorDisk)) :=
    (exterior_image_open_of_isOpen F hF exteriorDisk_isOpen subset_rfl).preimage
      (continuous_iff_continuousAt.mpr fun x => (hφ x (mem_univ x)).continuousAt)
  intro z hz
  have hE : (fun v => Real.log ‖exteriorInverse F (φ v)‖) =ᶠ[𝓝 z]
      exteriorGreenCoordinate F ∘ φ := by
    filter_upwards [ho.mem_nhds hz] with v hv
    change φ v ∈ F '' exteriorDisk at hv
    simp [exteriorGreenCoordinate,hv]
  rw [← InnerProductSpace.harmonicAt_congr_nhds hE]
  have hz' : φ z ∈ F '' exteriorDisk := hz
  have hi : AnalyticAt ℂ (exteriorInverse F) (φ z) := by
    obtain ⟨w,hw,he⟩ := hz'
    exact he ▸ exteriorInverse_analyticAt_image F hF w hw
  exact (hi.comp (hφ z (mem_univ z))).harmonicAt_log_norm
    (exterior_ne_zero (Function.invFunOn_mem hz'))

/-- The positive part of the potential above a positive cut level has
a uniform circle submean on any fixed compact set of centers. The
uniform radius avoids any interchange with a varying local radius. -/
theorem exteriorGreenCoordinate_clipped_uniform_submean
    (F φ : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hφ : AnalyticOnNhd ℂ φ univ)
    (τ : ℝ) (hτ : 0 < τ) (S : Set ℂ) (hS : IsCompact S) :
    let u := fun z : ℂ => max (exteriorGreenCoordinate F (φ z)-τ) 0
    ∃ δ > 0, ∀ z ∈ S, ∀ r > 0, r < δ → u z ≤ circleAverage u z r := by
  let g := exteriorGreenCoordinate F ∘ φ
  let u := fun z : ℂ => max (g z-τ) 0
  let C := S ∩ {z | τ ≤ g z}
  let U := φ ⁻¹' (F '' exteriorDisk)
  have hφc : Continuous φ := continuous_iff_continuousAt.mpr fun z => (hφ z (mem_univ z)).continuousAt
  have hg : Continuous g := (exteriorGreenCoordinate_continuous F hF).comp hφc
  have hu : Continuous u := (hg.sub continuous_const).max continuous_const
  have hC : IsCompact C := hS.inter_right (isClosed_le continuous_const hg)
  have hU : IsOpen U := (exterior_image_open_of_isOpen F hF exteriorDisk_isOpen subset_rfl).preimage hφc
  have hCU : C ⊆ U := by
    intro z hz
    exact (exteriorGreenCoordinate_pos_iff F (φ z)).mp (hτ.trans_le hz.2)
  obtain ⟨δ,hδ,hδsub⟩ := hC.exists_thickening_subset_open hU hCU
  refine ⟨δ,hδ,?_⟩
  intro z hz r hr hrδ
  change u z ≤ circleAverage u z r
  by_cases hgz : τ ≤ g z
  · have hs : closedBall z |r| ⊆ U := by
      intro w hw
      apply hδsub
      rw [mem_thickening_iff]
      exact ⟨z,⟨hz,hgz⟩,(show dist w z ≤ |r| from hw).trans_lt (by rwa [abs_of_pos hr])⟩
    have hH : InnerProductSpace.HarmonicOnNhd (fun w => g w-τ) (closedBall z |r|) :=
      ((exteriorGreenCoordinate_harmonicOnNhd_comp F φ hF hφ).mono hs).sub
        (by intro w hw; exact InnerProductSpace.harmonicAt_const τ)
    have h₁ : CircleIntegrable (fun w => g w-τ) z r :=
      (hg.sub continuous_const).continuousOn.circleIntegrable hr.le
    have h₂ : CircleIntegrable u z r := hu.continuousOn.circleIntegrable hr.le
    have hle : circleAverage (fun w => g w-τ) z r ≤ circleAverage u z r :=
      Real.circleAverage_mono h₁ h₂ (fun _ _ => le_max_left _ _)
    have he : circleAverage (fun w : ℂ => g w-τ) z r = g z-τ := hH.circleAverage_eq
    rw [he] at hle
    simpa only [u,max_eq_left (sub_nonneg.mpr hgz)] using hle
  · have he : u z = 0 := max_eq_right (sub_nonpos.mpr (le_of_not_ge hgz))
    rw [he]
    exact circleAverage_nonneg_of_nonneg fun w _ => le_max_right _ _

end SpringerLean
