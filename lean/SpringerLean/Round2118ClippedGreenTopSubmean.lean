import SpringerLean.Round2114ClippedGappedOptimizer
import SpringerLean.Round2116VerticalTopContinuity
import SpringerLean.Round2117VerticalCircleFubini
import SpringerLean.Round31PairAverage

open Set MeasureTheory Metric Real

namespace SpringerLean

noncomputable def clippedOddGreen (F : ℂ → ℂ) (τ : ℝ) (z : ℂ) : ℝ :=
  max (exteriorGreenCoordinate F (oddGreenChart z)-τ) 0

theorem clippedOddGreen_continuous (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (τ : ℝ) :
    Continuous (clippedOddGreen F τ) := by
  unfold clippedOddGreen
  have hc := exteriorGreenCoordinate_continuous F hF
  have hφ : Continuous oddGreenChart := by unfold oddGreenChart; fun_prop
  exact ((hc.comp hφ).sub continuous_const).max continuous_const

theorem clippedOddGreen_periodic (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (τ x : ℝ) :
    Function.Periodic (fun t : ℝ => clippedOddGreen F τ ((x:ℂ)+(t:ℂ)*Complex.I)) (2*π) :=
  fun t => congrArg (fun a : ℝ => max (a-τ) 0) (oddGreenChart_potential_periodic F hF ho x t)

private theorem circleMap_center_real_re (x ρ θ : ℝ) :
    (circleMap (x:ℂ) ρ θ).re = x+ρ*cos θ := by
  rw [show circleMap (x:ℂ) ρ θ = (x:ℂ)+circleMap 0 ρ θ by simp [circleMap]]
  simp [Complex.add_re,circleMap_zero_re]

private theorem circleMap_center_real_im (x ρ θ : ℝ) :
    (circleMap (x:ℂ) ρ θ).im = ρ*sin θ := by
  rw [show circleMap (x:ℂ) ρ θ = (x:ℂ)+circleMap 0 ρ θ by simp [circleMap]]
  simp [Complex.add_im,circleMap_zero_im]

/-- The top integral of the actual clipped Green profile satisfies the
local submean in the open angular strip. Both the optimizing set and
one uniform radius are built for the actual map. -/
theorem clippedOddGreen_top_local_submean
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (τ : ℝ) (hτ : 0 < τ)
    (x h : ℝ) (hh : 0 < h) (hπ : h < π) :
    let U := verticalPeriodicTop (clippedOddGreen F τ) (2*π)
    ∃ δ > 0, ∀ r > 0, r < δ → U ((x:ℂ)+(h:ℂ)*Complex.I) ≤
      circleAverage U ((x:ℂ)+(h:ℂ)*Complex.I) r := by
  let T := 2*π
  let u := clippedOddGreen F τ
  let U := verticalPeriodicTop u T
  let g (t : ℝ) := exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  have hφ : Continuous oddGreenChart := by unfold oddGreenChart; fun_prop
  have hgc : Continuous g := (exteriorGreenCoordinate_continuous F hF).comp (hφ.comp (by fun_prop))
  have hu := clippedOddGreen_continuous F hF τ
  have hper := clippedOddGreen_periodic F hF ho τ
  obtain ⟨q,p,d,E,hd,hEm,hEv,hEin,hEout,hEt⟩ :=
    clipped_periodic_exists_gapped_topIntegral g hgc T (2*h) τ two_pi_pos
      (oddGreenChart_potential_periodic F hF ho x) (by positivity) (by dsimp [T]; linarith) hτ
      (oddGreenChart_positive_level_volume_zero F hF x)
  let X (t : ℝ) := (x:ℂ)+(t:ℂ)*Complex.I
  let C := X '' Icc (q+d) (q+T-d)
  have hC : IsCompact C := isCompact_Icc.image (by unfold X; fun_prop)
  obtain ⟨b,hb,hsub⟩ := exteriorGreenCoordinate_clipped_uniform_submean F oddGreenChart hF
    oddGreenChart_analyticOnNhd τ hτ C hC
  let δ := min b (min d (min h (π-h)))
  have hδ : 0 < δ := lt_min hb (lt_min hd (lt_min hh (sub_pos.mpr hπ)))
  refine ⟨δ,hδ,?_⟩
  intro r hr hrδ
  have hrb : r < b := hrδ.trans_le (min_le_left _ _)
  have hrd : r < d := hrδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hrh : r < h := hrδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrπ : r < π-h := hrδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let Q (z : ℂ) := ∫ t in E, u (z+(t:ℂ)*Complex.I)
  let V (z : ℂ) := U (z+(h:ℂ)*Complex.I)
  have hEb := (isBounded_Icc _ _).subset hEout
  obtain ⟨hQi,hint,hswap⟩ := continuous_vertical_setIntegral_circleAverage u hu E hEm hEb (x:ℂ) r
  have hQ : Q (x:ℂ) ≤ circleAverage Q (x:ℂ) r := by
    rw [show circleAverage Q (x:ℂ) r = _ from hswap]
    have hi : IntegrableOn (fun t : ℝ => u ((x:ℂ)+(t:ℂ)*Complex.I)) E :=
      ((hu.comp (by fun_prop)).continuousOn.integrableOn_compact isCompact_Icc).mono_set hEout
    exact setIntegral_mono_on hi hint hEm (fun t ht => hsub (X t) ⟨t,hEout ht,rfl⟩ r hr hrb)
  have hUc := verticalPeriodicTop_continuousOn u hu (fun z => le_max_right _ _) T two_pi_pos hper
  have hVcircle : CircleIntegrable V (x:ℂ) r := by
    apply ContinuousOn.circleIntegrable'
    apply hUc.comp (by fun_prop) ?_
    intro z hz
    have hnorm : ‖z-(x:ℂ)‖ = r := by
      simpa only [mem_sphere,dist_eq_norm,abs_of_pos hr] using hz
    have hab : |z.im| ≤ r := by
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,hnorm] using Complex.abs_im_le_norm (z-(x:ℂ))
    change 0 ≤ (z+(h:ℂ)*Complex.I).im ∧ (z+(h:ℂ)*Complex.I).im ≤ T/2
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_im,Complex.I_re,mul_one,zero_mul,add_zero]
    exact ⟨by linarith [(abs_le.mp hab).1],by dsimp [T]; linarith [(abs_le.mp hab).2]⟩
  have hreal : U ((x:ℂ)+(h:ℂ)*Complex.I) = Q (x:ℂ) := by
    unfold U verticalPeriodicTop Q
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, sub_self, add_zero, zero_add]
    exact hEt
  have hpairQ := circleAverage_real_center_eq_angle_pair Q x r hQi
  have hpairV := circleAverage_real_center_eq_angle_pair V x r hVcircle
  have hiQ := circleIntegrable_angle_pair Q x r hQi
  have hiV := circleIntegrable_angle_pair V x r hVcircle
  have hcomp : ∀ θ ∈ Icc 0 π,
      Q (circleMap (x:ℂ) r θ)+Q (circleMap (x:ℂ) r (-θ)) ≤
        V (circleMap (x:ℂ) r θ)+V (circleMap (x:ℂ) r (-θ)) := by
    intro θ hθ
    let y := x+r*cos θ
    let e := r*sin θ
    let f (t : ℝ) := u ((y:ℂ)+(t:ℂ)*Complex.I)
    have hf : Continuous f := hu.comp (by fun_prop)
    have he0 : 0 ≤ e := mul_nonneg hr.le (sin_nonneg_of_mem_Icc hθ)
    have hed : e < d := (mul_le_of_le_one_right hr.le (sin_le_one θ)).trans_lt hrd
    have hCplus : circleMap (x:ℂ) r θ = (y:ℂ)+(e:ℂ)*Complex.I := by
      apply Complex.ext <;>
        simp only [y,e,circleMap_center_real_re,circleMap_center_real_im,Complex.add_re,Complex.add_im,
          Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
          mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
    have hCminus : circleMap (x:ℂ) r (-θ) = (y:ℂ)-(e:ℂ)*Complex.I := by
      apply Complex.ext <;>
        simp only [y,e,circleMap_center_real_re,circleMap_center_real_im,Complex.sub_re,Complex.sub_im,
          Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
          mul_zero,mul_one,zero_mul,sub_zero,zero_sub,add_zero,zero_add,cos_neg,sin_neg,mul_neg]
    have hQp : Q (circleMap (x:ℂ) r θ) = ∫ t in E, f (t+e) := by
      unfold Q f
      rw [hCplus]
      apply integral_congr_ae
      exact .of_forall (fun t => congrArg u (by push_cast; ring))
    have hQm : Q (circleMap (x:ℂ) r (-θ)) = ∫ t in E, f (t-e) := by
      unfold Q f
      rw [hCminus]
      apply integral_congr_ae
      exact .of_forall (fun t => congrArg u (by push_cast; ring))
    have hVp : V (circleMap (x:ℂ) r θ) = periodicTopIntegral f T (2*h+2*e) := by
      rw [hCplus]
      unfold V U verticalPeriodicTop
      simp [f,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,mul_add,add_comm]
    have hVm : V (circleMap (x:ℂ) r (-θ)) = periodicTopIntegral f T (2*h-2*e) := by
      rw [hCminus]
      unfold V U verticalPeriodicTop
      simp [f,Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.mul_re,
        Complex.mul_im,mul_add]
      ring_nf
    rw [hQp,hQm,hVp,hVm,add_comm (∫ t in E, f (t+e))]
    exact periodicTopIntegral_pair_ge_of_gapped_set f hf two_pi_pos (hper y) he0 hed E hEm hEv hEin hEout
  have hQV : circleAverage Q (x:ℂ) r ≤ circleAverage V (x:ℂ) r := by
    rw [hpairQ,hpairV]
    exact mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono_on pi_pos.le hiQ hiV hcomp)
      (inv_nonneg.mpr two_pi_pos.le)
  have hV : circleAverage V (x:ℂ) r = circleAverage U ((x:ℂ)+(h:ℂ)*Complex.I) r := by
    rw [circleAverage_eq_angle_Ioc_general,circleAverage_eq_angle_Ioc_general]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun θ => congrArg U (by simp only [circleMap,V]; ring)
  change U ((x:ℂ)+(h:ℂ)*Complex.I) ≤ _
  rw [hreal,← hV]
  exact hQ.trans hQV

end SpringerLean
