import SpringerLean.Round2118ClippedGreenTopSubmean
import SpringerLean.Round2121PeriodicTopEndpoints

open MeasureTheory Set Real

namespace SpringerLean

theorem oddGreenChart_surj_on_radius (x : ℝ) (w : ℂ) (hw : ‖w‖ = exp (x/2)) :
    ∃ t : ℝ, oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I) = w := by
  refine ⟨2*Complex.arg w-π,?_⟩
  rw [oddGreenChart_eq_circleMap,show π/2+(2*Complex.arg w-π)/2 = Complex.arg w by ring,
    ← hw,circleMap_zero,Complex.norm_mul_exp_arg_mul_I]

theorem oddGreenChart_integral_eq_circleAverage
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (x : ℝ) :
    (∫ t in Ioc (-π) π, exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))) =
      (2*π)*circleAverage (exteriorGreenCoordinate F) 0 (exp (x/2)) := by
  let G := exteriorGreenCoordinate F
  let r := exp (x/2)
  let g (t : ℝ) := G (circleMap 0 r t)
  have hπ : -π ≤ π := by linarith [pi_pos]
  have hgc : Continuous g := (exteriorGreenCoordinate_continuous F hF).comp (continuous_circleMap _ _)
  have hgp : Function.Periodic g π := by
    intro t
    have hC : circleMap 0 r (t+π) = -circleMap 0 r t := by
      rw [circleMap_zero,circleMap_zero,Complex.ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
      ring
    change G (circleMap 0 r (t+π)) = G (circleMap 0 r t)
    rw [hC]
    exact exteriorGreenCoordinate_neg_of_odd F hF ho _
  have hhalf : (∫ t in π..2*π, g t) = ∫ t in 0..π, g t := by
    simpa only [show π+π = 2*π by ring,zero_add] using hgp.intervalIntegral_add_eq π 0
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable (μ := volume) 0 π)
    (hgc.intervalIntegrable (μ := volume) π (2*π))
  rw [hhalf] at hsplit
  rw [←intervalIntegral.integral_of_le hπ,circleAverage_def,smul_eq_mul]
  simp_rw [oddGreenChart_eq_circleMap]
  change (∫ t in -π..π, g (π/2+t/2)) = (2*π)*((2*π)⁻¹*∫ t in 0..2*π, g t)
  have hswap : (∫ t in -π..π, g (π/2+t/2)) = 2*(∫ t in 0..π, g t) := by
    simpa only [add_comm (π/2),show -π/2+π/2 = (0:ℝ) by ring,show π/2+π/2 = π by ring,smul_eq_mul] using
      intervalIntegral.integral_comp_div_add (f := g) (a := -π) (b := π) (c := (2:ℝ)) (by norm_num) (π/2)
  rw [hswap,← mul_assoc,mul_inv_cancel₀ two_pi_pos.ne',one_mul,←hsplit]
  ring

theorem clippedOddGreen_top_full_flat_of_omitted_on_radius
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (τ : ℝ) (hτ : 0 < τ)
    (x : ℝ) (w : ℂ) (hw : ‖w‖ = exp (x/2)) (hwK : w ∈ exteriorOmitted F) :
    let U := verticalPeriodicTop (clippedOddGreen F τ) (2*π)
    ∃ δ > 0, ∀ d > 0, d < δ →
      U ((x:ℂ)+(π:ℂ)*Complex.I) ≤ U ((x:ℂ)+((π-d:ℝ):ℂ)*Complex.I) := by
  let U := verticalPeriodicTop (clippedOddGreen F τ) (2*π)
  let g (t : ℝ) := exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  let f (t : ℝ) := clippedOddGreen F τ ((x:ℂ)+(t:ℂ)*Complex.I)
  have hgc : Continuous g := by
    unfold g
    exact (exteriorGreenCoordinate_continuous F hF).comp (by unfold oddGreenChart; fun_prop)
  have hfc : Continuous f := (clippedOddGreen_continuous F hF τ).comp (by fun_prop)
  obtain ⟨q,hq⟩ := oddGreenChart_surj_on_radius x w hw
  have hgq : g q < τ := by
    change exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(q:ℂ)*Complex.I)) < τ
    rw [hq]
    have he : exteriorGreenCoordinate F w = 0 :=
      le_antisymm (le_of_not_gt (fun h => hwK ((exteriorGreenCoordinate_pos_iff F w).mp h)))
        (exteriorGreenCoordinate_nonneg F w)
    rwa [he]
  obtain ⟨r,hr,hsmall⟩ := Metric.isOpen_iff.mp (isOpen_lt hgc continuous_const) q hgq
  let δ := min (r/2) π
  refine ⟨δ,lt_min (half_pos hr) pi_pos,?_⟩
  intro d hd hdδ
  have hdr : 2*d < r := by linarith [hdδ.trans_le (min_le_left _ _)]
  have hdp : 2*d ≤ 2*π := by linarith [hdδ.trans_le (min_le_right _ _)]
  have hz (t : ℝ) (ht : t ∈ Ioc q (q+2*d)) : f t = 0 := by
    have hb : t ∈ Metric.ball q r := by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      linarith [ht.2]
    exact max_eq_right (sub_nonpos.mpr (hsmall hb).le)
  have hs := periodicTopIntegral_full_le_of_zero_arc f hfc (2*π) two_pi_pos
    (clippedOddGreen_periodic F hF ho τ x) (fun _ => le_max_right _ _) q (2*d) (by positivity) hdp
    (by simpa only [mul_assoc] using hz)
  unfold verticalPeriodicTop
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  rw [show 2*(π-d) = 2*π-2*d by ring]
  exact hs

end SpringerLean
