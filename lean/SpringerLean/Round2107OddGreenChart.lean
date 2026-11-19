import SpringerLean.Round2104SlitGreenEllipses
import SpringerLean.Round2105ClippedGreenSubmean
import SpringerLean.Round2096GreenRadialHinge
import Mathlib.Topology.Order.IntermediateValue

open Set MeasureTheory Real

namespace SpringerLean

/-- Logarithmic chart going from the upper and lower strip edges to
the two real rays. The square in the log radius accounts for oddness. -/
noncomputable def oddGreenChart (z : ℂ) : ℂ := Complex.I*Complex.exp (z/2)

theorem oddGreenChart_analyticOnNhd : AnalyticOnNhd ℂ oddGreenChart univ := by
  intro z hz
  unfold oddGreenChart
  fun_prop

theorem oddGreenChart_vertical_period (x t : ℝ) :
    oddGreenChart ((x:ℂ)+((t+2*π:ℝ):ℂ)*Complex.I) =
      -oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I) := by
  rw [oddGreenChart,oddGreenChart]
  rw [show ((x:ℂ)+((t+2*π:ℝ):ℂ)*Complex.I)/2 =
    ((x:ℂ)+(t:ℂ)*Complex.I)/2 + (π:ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add,Complex.exp_pi_mul_I]
  ring

theorem oddGreenChart_eq_circleMap (x t : ℝ) :
    oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I) = circleMap 0 (exp (x/2)) (π/2+t/2) := by
  rw [oddGreenChart,circleMap_zero]
  rw [show ((x:ℂ)+(t:ℂ)*Complex.I)/2 = ((x/2:ℝ):ℂ)+((t/2:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add, Complex.ofReal_exp]
  rw [Complex.ofReal_add,add_mul,Complex.exp_add]
  have he : Complex.exp (((π/2:ℝ):ℂ)*Complex.I) = Complex.I := by
    push_cast
    exact Complex.exp_pi_div_two_mul_I
  rw [he]
  ring

theorem oddGreenChart_im_pos (x t : ℝ) (h₁ : -π < t) (h₂ : t < π) :
    0 < (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)).im := by
  rw [oddGreenChart_eq_circleMap,circleMap_zero_im]
  exact mul_pos (exp_pos _) (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

theorem oddGreenChart_potential_periodic
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (x : ℝ) :
    Function.Periodic (fun t : ℝ => exteriorGreenCoordinate F
      (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))) (2*π) := by
  intro t
  change exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+((t+2*π:ℝ):ℂ)*Complex.I)) = _
  rw [oddGreenChart_vertical_period, exteriorGreenCoordinate_neg_of_odd F hF ho]

theorem exteriorGreenCoordinate_circleAverage_of_radius_bound
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (r : ℝ) (hr : 0 < r)
    (hR : ∀ z ∈ exteriorOmitted F, ‖z‖ ≤ r) :
    circleAverage (exteriorGreenCoordinate F) 0 r = log r := by
  rw [exteriorGreenCoordinate_circleAverage_eq_radial_hinge F hF r hr]
  have h := actualExteriorBoundaryProbability_ae_mem_omitted F hF
    (exteriorOmitted_isCompact F hF).isClosed
  have he : (∫ z, posLog (r⁻¹*‖z‖) ∂actualExteriorBoundaryProbability F) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h] with z hz
    change posLog (r⁻¹*‖z‖) = 0
    have hn : 0 ≤ r⁻¹*‖z‖ := by positivity
    rw [posLog_eq_zero_iff, abs_of_nonneg hn]
    exact (inv_mul_le_one₀ hr).2 (hR z hz)
  rw [he,add_zero]

/-- A connected omitted set containing zero meets every centered circle
up to its maximal radius. Its actual Green coordinate vanishes there. -/
theorem exteriorGreenCoordinate_has_zero_on_radius
    (F : ℂ → ℂ) (hc : IsConnected (exteriorOmitted F))
    (h0 : (0:ℂ) ∈ exteriorOmitted F) (w : ℂ) (hw : w ∈ exteriorOmitted F)
    (r : ℝ) (hr : 0 ≤ r) (hrw : r ≤ ‖w‖) :
    ∃ z ∈ exteriorOmitted F, ‖z‖ = r ∧ exteriorGreenCoordinate F z = 0 := by
  classical
  let K := exteriorOmitted F
  have h := (hc.image norm continuous_norm.continuousOn).isPreconnected.ordConnected
  have ha : (0:ℝ) ∈ norm '' K := by simpa using mem_image_of_mem norm h0
  have hb : ‖w‖ ∈ norm '' K := mem_image_of_mem norm hw
  obtain ⟨z,hz,hzr⟩ := h.out ha hb ⟨hr,hrw⟩
  refine ⟨z,hz,hzr,?_⟩
  exact le_antisymm (le_of_not_gt (fun h' => hz ((exteriorGreenCoordinate_pos_iff F z).mp h')))
    (exteriorGreenCoordinate_nonneg F z)

end SpringerLean
