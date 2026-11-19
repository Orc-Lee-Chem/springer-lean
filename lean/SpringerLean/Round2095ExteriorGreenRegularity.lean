import SpringerLean.Round2091ActualFactorFormula
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

open Set Filter Real Metric MeasureTheory
open scoped Topology

namespace SpringerLean

theorem exteriorGreenCoordinate_nonneg (F : ℂ → ℂ) (x : ℂ) :
    0 ≤ exteriorGreenCoordinate F x := by
  classical
  by_cases hx : x ∈ F '' exteriorDisk
  · have ht : 1 < ‖exteriorInverse F x‖ := Function.invFunOn_mem hx
    rw [exteriorGreenCoordinate, if_pos hx]
    exact Real.log_nonneg ht.le
  · simp [exteriorGreenCoordinate,hx]

theorem exteriorGreenCoordinate_le_on_collar
    (F : ℂ → ℂ) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (z : ℂ)
    (hz : z ∈ exteriorOmittedAtScale F s) :
    exteriorGreenCoordinate F z ≤ Real.log s⁻¹ := by
  classical
  have hs : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
  by_cases h : z ∈ F '' exteriorDisk
  · have hle : ‖exteriorInverse F z‖ ≤ s⁻¹ := by
      by_contra! hlt
      exact hz ⟨exteriorInverse F z,hlt,Function.invFunOn_eq h⟩
    have hpos : 0 < ‖exteriorInverse F z‖ := lt_trans zero_lt_one
      (show 1 < ‖exteriorInverse F z‖ from Function.invFunOn_mem h)
    rw [exteriorGreenCoordinate, if_pos h]
    exact Real.log_le_log hpos hle
  · rw [exteriorGreenCoordinate, if_neg h]
    exact Real.log_nonneg hs.le

/-- The zero extension is continuous also at every actual omitted
point, by the outer collars. -/
theorem exteriorGreenCoordinate_continuous
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) :
    Continuous (exteriorGreenCoordinate F) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ F '' exteriorDisk
  · have hOpen := exterior_image_open_of_isOpen F hF exteriorDisk_isOpen subset_rfl
    have hA : AnalyticAt ℂ (exteriorInverse F) x := by
      obtain ⟨w,hw,rfl⟩ := hx
      exact exteriorInverse_analyticAt_image F hF w hw
    have hnorm : 1 < ‖exteriorInverse F x‖ := Function.invFunOn_mem hx
    have hc := hA.continuousAt.norm.log (ne_of_gt (lt_trans zero_lt_one hnorm))
    have he : (fun z => Real.log ‖exteriorInverse F z‖) =ᶠ[𝓝 x] exteriorGreenCoordinate F := by
      filter_upwards [hOpen.mem_nhds hx] with z hz
      simp [exteriorGreenCoordinate,hz]
    exact hc.congr he
  · rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    let s := Real.exp (-ε/2)
    have hs0 : 0 < s := Real.exp_pos _
    have hs1 : s < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hC : exteriorOmittedAtScale F s ∈ 𝓝 x :=
      mem_interior_iff_mem_nhds.mp (exteriorOmitted_mem_interior_atScale F hF x hx s hs0 hs1)
    filter_upwards [hC] with z hz
    have hle := exteriorGreenCoordinate_le_on_collar F s hs0 hs1 z hz
    have hslog : Real.log s⁻¹ = ε/2 := by simp [s, Real.log_inv]; ring
    rw [hslog] at hle
    rw [show exteriorGreenCoordinate F x = 0 by simp [exteriorGreenCoordinate,hx],
      Real.dist_eq, sub_zero, abs_of_nonneg (exteriorGreenCoordinate_nonneg F z)]
    linarith

/-- In logarithmic polar coordinates the Green coordinate is harmonic
where it is positive, and has the local circle submean everywhere. -/
theorem exteriorGreenCoordinate_logPolar_local_submean
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (x : ℂ) :
    let G := exteriorGreenCoordinate F ∘ Complex.exp
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      G x ≤ circleAverage G x r := by
  classical
  let G := exteriorGreenCoordinate F ∘ Complex.exp
  let U := Complex.exp ⁻¹' (F '' exteriorDisk)
  have hU : IsOpen U := (exterior_image_open_of_isOpen F hF exteriorDisk_isOpen subset_rfl).preimage
    Complex.continuous_exp
  by_cases hx : x ∈ U
  · have hH : InnerProductSpace.HarmonicOnNhd G U := by
      intro z hz
      have he : (fun v => Real.log ‖exteriorInverse F (Complex.exp v)‖) =ᶠ[𝓝 z] G := by
        filter_upwards [hU.mem_nhds hz] with v hv
        change Complex.exp v ∈ F '' exteriorDisk at hv
        simp [G, exteriorGreenCoordinate,hv]
      rw [← InnerProductSpace.harmonicAt_congr_nhds he]
      have hv : Complex.exp z ∈ F '' exteriorDisk := hz
      have hA : AnalyticAt ℂ (exteriorInverse F) (Complex.exp z) := by
        obtain ⟨w,hw,heq⟩ := hv
        exact heq ▸ exteriorInverse_analyticAt_image F hF w hw
      exact (hA.comp analyticAt_cexp).harmonicAt_log_norm
        (exterior_ne_zero (Function.invFunOn_mem hv))
    obtain ⟨δ,hδ,hsub⟩ := Metric.isOpen_iff.mp hU x hx
    refine ⟨δ,hδ,?_⟩
    intro r hr hlt
    have hball : closedBall x |r| ⊆ U :=
      (closedBall_subset_ball (by rwa [abs_of_pos hr])).trans hsub
    exact (hH.mono hball).circleAverage_eq.ge
  · refine ⟨1,zero_lt_one,?_⟩
    intro r _ _
    change Complex.exp x ∉ F '' exteriorDisk at hx
    have he : G x = 0 := by simp [G,exteriorGreenCoordinate,hx]
    change G x ≤ circleAverage G x r
    rw [he]
    exact circleAverage_nonneg_of_nonneg (fun z _ => exteriorGreenCoordinate_nonneg F (Complex.exp z))

end SpringerLean
