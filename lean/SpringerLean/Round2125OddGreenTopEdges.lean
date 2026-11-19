import SpringerLean.Round2120SlitTopHarmonic
import SpringerLean.Round2124GreenAsymptotics

open Set Real MeasureTheory

namespace SpringerLean

theorem slitGreenTop_continuousOn :
    ContinuousOn slitGreenTop {z : ℂ | 0 ≤ z.im ∧ z.im ≤ π} := by
  have hs := slitMap_centeredExteriorUnivalent 1 (by simp)
  have hφ : Continuous oddGreenChart := by unfold oddGreenChart; fun_prop
  have hv := (exteriorGreenCoordinate_continuous (slitMap 1) hs).comp hφ
  change ContinuousOn (verticalPeriodicTop (exteriorGreenCoordinate (slitMap 1) ∘ oddGreenChart) (2*π)) _
  simpa only [show 2*π/2 = π by ring] using
    verticalPeriodicTop_continuousOn _ hv (fun z => exteriorGreenCoordinate_nonneg _ _) _ two_pi_pos
      (oddGreenChart_potential_periodic _ hs (fun z _ => slitMap_one_odd z))

theorem slitGreenTop_eq_arc (x h : ℝ) (h₀ : 0 ≤ h) (hπ : h ≤ π) :
    slitGreenTop ((x:ℂ)+(h:ℂ)*Complex.I) =
      ∫ t in Ioc (-h) h, exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)) := by
  unfold slitGreenTop verticalPeriodicTop
  simp only [Function.comp_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  exact slitGreenChart_topIntegral_eq_arc x h h₀ hπ

theorem slitGreenTop_mono_height (x h h' : ℝ) (h₀ : 0 ≤ h) (hle : h ≤ h') (hπ : h' ≤ π) :
    slitGreenTop ((x:ℂ)+(h:ℂ)*Complex.I) ≤ slitGreenTop ((x:ℂ)+(h':ℂ)*Complex.I) := by
  rw [slitGreenTop_eq_arc x h h₀ (hle.trans hπ),slitGreenTop_eq_arc x h' (h₀.trans hle) hπ]
  let f (t : ℝ) := exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  have hf : Continuous f := (exteriorGreenCoordinate_continuous _
    (slitMap_centeredExteriorUnivalent 1 (by simp))).comp (by unfold oddGreenChart; fun_prop)
  have hi : IntegrableOn f (Ioc (-h') h') :=
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  exact setIntegral_mono_set hi (.of_forall (fun t => exteriorGreenCoordinate_nonneg _ _))
    (.of_forall (fun _ ht => ⟨(neg_le_neg hle).trans_lt ht.1,ht.2.trans hle⟩))

theorem clippedOddGreen_top_full_le_slit_of_radius_bound
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F)
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (τ : ℝ) (hτ : 0 ≤ τ) (x : ℝ)
    (hR : ∀ z ∈ exteriorOmitted F, ‖z‖ ≤ exp (x/2)) :
    verticalPeriodicTop (clippedOddGreen F τ) (2*π) ((x:ℂ)+(π:ℂ)*Complex.I) ≤
      slitGreenTop ((x:ℂ)+(π:ℂ)*Complex.I) := by
  let f (t : ℝ) := clippedOddGreen F τ ((x:ℂ)+(t:ℂ)*Complex.I)
  let g (t : ℝ) := exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  let r := exp (x/2)
  have hr : 0 < r := exp_pos _
  have hfc : Continuous f := (clippedOddGreen_continuous F hF τ).comp (by fun_prop)
  have hgc : Continuous g := (exteriorGreenCoordinate_continuous _ hF).comp (by unfold oddGreenChart; fun_prop)
  have hi (v : ℝ → ℝ) (hv : Continuous v) : IntegrableOn v (Ioc (-π) π) :=
    (hv.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h := periodicTopIntegral_full_of_nonneg f hfc (2*π) two_pi_pos
    (clippedOddGreen_periodic F hF ho τ x) (fun _ => le_max_right _ _) (-π)
  rw [show -π+2*π = π by ring] at h
  unfold verticalPeriodicTop
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add]
  change periodicTopIntegral f (2*π) (2*π) ≤ _
  rw [h,slitGreenTop_eq_arc x π pi_pos.le le_rfl,oddGreenChart_integral_eq_circleAverage (slitMap 1)
    (slitMap_centeredExteriorUnivalent 1 (by simp)) (fun z _ => slitMap_one_odd z)]
  have hfg : (∫ t in Ioc (-π) π, f t) ≤ ∫ t in Ioc (-π) π, g t := by
    apply setIntegral_mono_on (hi f hfc) (hi g hgc) measurableSet_Ioc
    intro t _
    exact max_le (sub_le_self _ hτ) (exteriorGreenCoordinate_nonneg _ _)
  change (∫ t in Ioc (-π) π, f t) ≤ (2*π)*circleAverage (exteriorGreenCoordinate (slitMap 1)) 0 r
  apply hfg.trans
  rw [show (∫ t in Ioc (-π) π, g t) = (2*π)*circleAverage (exteriorGreenCoordinate F) 0 r from
    oddGreenChart_integral_eq_circleAverage F hF ho x,
    exteriorGreenCoordinate_circleAverage_of_radius_bound F hF r hr hR,
    exteriorGreenCoordinate_circleAverage_eq_radial_hinge _
      (slitMap_centeredExteriorUnivalent 1 (by simp)) _ hr]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right
    (integral_nonneg (fun _ => posLog_nonneg))) two_pi_pos.le

end SpringerLean
