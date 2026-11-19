import SpringerLean.Round2107OddGreenChart
import SpringerLean.Round2106PeriodicTopIntegral

open Set MeasureTheory Real

namespace SpringerLean

theorem slitMap_one_odd (z : ℂ) : slitMap 1 (-z) = -slitMap 1 z := by
  simp [slitMap,div_neg]
  ring

theorem oddGreenChart_abs_re (x t : ℝ) (ht : |t| ≤ π) :
    |(oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)).re| = exp (x/2)*sin (|t|/2) := by
  rw [oddGreenChart_eq_circleMap,circleMap_zero_re,Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two,
    zero_mul,one_mul,zero_sub,abs_mul,abs_neg,abs_of_pos (exp_pos _),
    Real.abs_sin_eq_sin_abs_of_abs_le_pi, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [Real.pi_pos]

theorem oddGreenChart_norm (x t : ℝ) :
    ‖oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)‖ = exp (x/2) := by
  simp [oddGreenChart_eq_circleMap, norm_circleMap_zero, abs_of_pos (exp_pos _)]

/-- The slit comparison on a centered angular turn in the log chart. -/
theorem slitGreenChart_value_le_of_abs_angle_le (x s t : ℝ) (hst : |s| ≤ |t|) (ht : |t| ≤ π) :
    exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)) ≤
      exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(s:ℂ)*Complex.I)) := by
  apply slitGreen_antitone_abs_re_of_norm_eq
  · rw [oddGreenChart_norm,oddGreenChart_norm]
  · rw [oddGreenChart_abs_re x s (hst.trans ht),oddGreenChart_abs_re x t ht]
    exact mul_le_mul_of_nonneg_left
      (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg s, Real.pi_pos])
        (by linarith) (by linarith)) (exp_pos _).le

theorem slitGreenChart_value_neg_angle (x t : ℝ) (ht : |t| ≤ π) :
    exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+((-t:ℝ):ℂ)*Complex.I)) =
      exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I)) := by
  apply le_antisymm
  · exact slitGreenChart_value_le_of_abs_angle_le x t (-t) (by simp) (by simpa using ht)
  · exact slitGreenChart_value_le_of_abs_angle_le x (-t) t (by simp) ht

/-- The actual integral of the highest angular mass for the slit is
the integral on the centered arc. -/
theorem slitGreenChart_topIntegral_eq_arc (x h : ℝ) (h₀ : 0 ≤ h) (hπ : h ≤ π) :
    let f := fun t : ℝ => exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
    periodicTopIntegral f (2*π) (2*h) = ∫ t in Ioc (-h) h, f t := by
  let f := fun t : ℝ => exteriorGreenCoordinate (slitMap 1) (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  have hF := slitMap_centeredExteriorUnivalent 1 (by simp)
  have hchart : Continuous oddGreenChart := by unfold oddGreenChart; fun_prop
  have hfc : Continuous f := (exteriorGreenCoordinate_continuous _ hF).comp
    (hchart.comp (by fun_prop))
  have hp : Function.Periodic f (2*π) := oddGreenChart_potential_periodic _ hF
    (fun z _ => slitMap_one_odd z) x
  change periodicTopIntegral f (2*π) (2*h) = ∫ t in Ioc (-h) h, f t
  apply periodicTopIntegral_eq_of_threshold_set f hfc (2*π) (2*h) two_pi_pos hp (by linarith)
    (by linarith) (-π) (f h) _ measurableSet_Ioc
  · intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [volume_real_Ioc_of_le (by linarith : -h ≤ h)]
    ring
  · intro t ht
    exact slitGreenChart_value_le_of_abs_angle_le x t h
      (by rw [abs_of_nonneg h₀]; exact abs_le.mpr ⟨ht.1.le,ht.2⟩)
      (by simpa [abs_of_nonneg h₀] using hπ)
  · intro t ht htn
    have ha : |h| ≤ |t| := by
      rw [abs_of_nonneg h₀]
      by_contra! hh
      exact htn ⟨(abs_lt.mp hh).1,(abs_lt.mp hh).2.le⟩
    exact slitGreenChart_value_le_of_abs_angle_le x h t ha
      (abs_le.mpr ⟨ht.1.le,by linarith [ht.2]⟩)

end SpringerLean
