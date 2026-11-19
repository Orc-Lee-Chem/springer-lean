import SpringerLean.Round2119SlitAnalyticLog
import SpringerLean.Round2116VerticalTopContinuity
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RealDeriv

open Set Filter Metric Real MeasureTheory
open scoped Topology

namespace SpringerLean

noncomputable def slitGreenTop (z : ℂ) : ℝ :=
  verticalPeriodicTop (exteriorGreenCoordinate (slitMap 1) ∘ oddGreenChart) (2*π) z

private theorem norm_vert_sub_real_sq (s t x : ℝ) :
    ‖(s:ℂ)+(t:ℂ)*Complex.I-(x:ℂ)‖^2 = (s-x)^2+t^2 := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
  simp [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring

private theorem vert_dist_le_of_abs_im_le (w : ℂ) (x t : ℝ) (ht : |t| ≤ |w.im|) :
    dist ((w.re:ℂ)+(t:ℂ)*Complex.I) (x:ℂ) ≤ dist w (x:ℂ) := by
  rw [dist_eq_norm,dist_eq_norm]
  apply le_of_sq_le_sq _ (norm_nonneg _)
  have hw : ‖w-(x:ℂ)‖^2 = (w.re-x)^2+w.im^2 :=
    (congrArg (fun z : ℂ => ‖z-(x:ℂ)‖^2) (Complex.re_add_im w).symm).trans
      (norm_vert_sub_real_sq w.re w.im x)
  rw [norm_vert_sub_real_sq,hw]
  have h : t^2 ≤ w.im^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) ht 2
  linarith only [h]

private theorem hasDerivAt_im_vertical {P : ℂ → ℂ} {a : ℂ} {x t : ℝ}
    (h : HasDerivAt P a ((x:ℂ)+(t:ℂ)*Complex.I)) :
    HasDerivAt (fun s : ℝ => (P ((x:ℂ)+(s:ℂ)*Complex.I)).im) a.re t := by
  have hi : HasDerivAt (fun s : ℂ => (x:ℂ)+s*Complex.I) Complex.I (t:ℂ) := by
    simpa using (hasDerivAt_id (t:ℂ)).mul_const Complex.I |>.const_add (x:ℂ)
  have hC := h.comp (t:ℂ) hi
  have hR := hC.comp_ofReal
  have he : HasDerivAt (fun s : ℝ => (P ((x:ℂ)+(s:ℂ)*Complex.I)).im) (a*Complex.I).im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hR
  simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero] using he

private theorem hasDerivAt_im_horizontal {P : ℂ → ℂ} {a : ℂ} {x : ℝ}
    (h : HasDerivAt P a (x:ℂ)) :
    HasDerivAt (fun s : ℝ => (P (s:ℂ)).im) a.im x := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h.comp_ofReal

/-- The slit top integral is harmonic in the open upper strip. A disk
covering the centered arc has a holomorphic primitive of the inverse
logarithm. On the center line its imaginary part is constant. -/
theorem slitGreenTop_harmonicOnNhd :
    InnerProductSpace.HarmonicOnNhd slitGreenTop {z : ℂ | 0 < z.im ∧ z.im < π} := by
  intro z hz
  let x := z.re
  let R := (z.im+π)/2
  let B := ball (x:ℂ) R
  have hxzr : dist z (x:ℂ) = z.im := by
    have he : z-(x:ℂ) = (z.im:ℂ)*Complex.I := by
      dsimp [x]
      nth_rw 1 [←Complex.re_add_im z]
      ring
    rw [dist_eq_norm,he,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1]
  have hzB : z ∈ B := by change dist z (x:ℂ) < R; rw [hxzr]; dsimp [R]; linarith [hz.2]
  have hR : 0 < R := by dsimp [R]; linarith [hz.1,pi_pos]
  have hBS : B ⊆ oddGreenOpenStrip := by
    intro w hw
    have h := Complex.abs_im_le_norm (w-(x:ℂ))
    rw [Complex.sub_im,Complex.ofReal_im,sub_zero,←dist_eq_norm] at h
    have hw' : dist w (x:ℂ) < R := hw
    have hlt := h.trans_lt hw'
    exact ⟨by dsimp [R] at hlt; linarith [(abs_lt.mp hlt).1,hz.2],
      by dsimp [R] at hlt; linarith [(abs_lt.mp hlt).2,hz.2]⟩
  let A := slitGreenAnalyticLog
  have hA : DifferentiableOn ℂ A B :=
    (slitGreenAnalyticLog_analyticOnNhd.mono hBS).differentiableOn
  obtain ⟨P,hP⟩ := hA.isExactOn_ball
  have hPa : AnalyticOnNhd ℂ P B :=
    (show DifferentiableOn ℂ P B from fun w hw => (hP w hw).differentiableAt.differentiableWithinAt).analyticOnNhd
      isOpen_ball
  let V (w : ℂ) := exteriorGreenCoordinate (slitMap 1) (oddGreenChart w)
  have hVc : Continuous V := (exteriorGreenCoordinate_continuous _
    (slitMap_centeredExteriorUnivalent 1 (by simp))).comp (by unfold oddGreenChart; fun_prop)
  have hform : ∀ w ∈ B, 0 < w.im → w.im < π →
      slitGreenTop w = (2*P w-2*P (x:ℂ)).im := by
    intro w hw hwi hwp
    let y := w.re
    let h := w.im
    have h₀ : 0 ≤ h := hwi.le
    let p (t : ℝ) := (y:ℂ)+(t:ℂ)*Complex.I
    have hv (t : ℝ) (ht : t ∈ Icc 0 h) : p t ∈ B := by
      have hab : |t| ≤ |w.im| := by rw [abs_of_nonneg ht.1,abs_of_pos hwi]; exact ht.2
      exact (vert_dist_le_of_abs_im_le w x t hab).trans_lt hw
    have hhor (t : ℝ) (ht : t ∈ uIcc x y) : (t:ℂ) ∈ B := by
      have hab : |t-x| ≤ |y-x| := by
        rcases le_total x y with hh | hh
        · rw [uIcc_of_le hh] at ht
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1),abs_of_nonneg (sub_nonneg.mpr hh)]
          linarith [ht.2]
        · rw [uIcc_of_ge hh] at ht
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2),abs_of_nonpos (sub_nonpos.mpr hh)]
          linarith [ht.1]
      have hdist : |y-x| ≤ dist w (x:ℂ) := by
        rw [dist_eq_norm]
        simpa [y,Complex.sub_re] using Complex.abs_re_le_norm (w-(x:ℂ))
      change dist (t:ℂ) (x:ℂ) < R
      rw [dist_eq_norm,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact hab.trans_lt (hdist.trans_lt hw)
    have hx0 : (P (y:ℂ)).im = (P (x:ℂ)).im := by
      have hD (t : ℝ) (ht : t ∈ uIcc x y) :
          HasDerivAt (fun s : ℝ => (P (s:ℂ)).im) 0 t := by
        have h := hasDerivAt_im_horizontal (hP _ (hhor t ht))
        simpa only [A,slitGreenAnalyticLog_im_real] using h
      have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hD (intervalIntegrable_const (c := (0:ℝ)))
      have hz0 : (P (y:ℂ)).im-(P (x:ℂ)).im = 0 := by simpa using he.symm
      exact sub_eq_zero.mp hz0
    have hder (t : ℝ) (ht : t ∈ uIcc 0 h) : HasDerivAt (fun s : ℝ => (P (p s)).im) (V (p t)) t := by
      have hpB := hv t (by simpa only [uIcc_of_le h₀] using ht)
      have hf := hasDerivAt_im_vertical (hP _ hpB)
      rw [slitGreenAnalyticLog_re _ (hBS hpB)] at hf
      exact hf
    have hi : ∀ a b : ℝ, IntervalIntegrable (fun t => V (p t)) volume a b :=
      (hVc.comp (by unfold p; fun_prop)).intervalIntegrable
    have hVder := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hi 0 h)
    have hv0 : p 0 = (y:ℂ) := by simp [p]
    have hvh : p h = w := Complex.re_add_im w
    rw [hv0,hvh,hx0] at hVder
    have hleft : (∫ t in -h..0, V (p t)) = ∫ t in 0..h, V (p t) := by
      have he := intervalIntegral.integral_comp_neg (fun t => V (p t)) (a := 0) (b := h)
      rw [neg_zero] at he
      rw [← he]
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc 0 h := by simpa only [uIcc_of_le h₀] using ht
      exact slitGreenChart_value_neg_angle y t (by rw [abs_of_nonneg ht'.1]; exact ht'.2.trans hwp.le)
    change periodicTopIntegral (fun t => V (p t)) (2*π) (2*h) = _
    rw [show periodicTopIntegral (fun t => V (p t)) (2*π) (2*h) = ∫ t in Ioc (-h) h, V (p t) from
      slitGreenChart_topIntegral_eq_arc y h hwi.le hwp.le,
      ← intervalIntegral.integral_of_le (by linarith : -h ≤ h),
      ← intervalIntegral.integral_add_adjacent_intervals (hi (-h) 0) (hi 0 h),hleft,hVder]
    simp [Complex.sub_im,Complex.mul_im]
    ring
  have hZB : B ∈ 𝓝 z := isOpen_ball.mem_nhds hzB
  have hZim : {w : ℂ | 0 < w.im ∧ w.im < π} ∈ 𝓝 z :=
    ((isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)).mem_nhds hz
  have hEq : (fun w => (2*P w-2*P (x:ℂ)).im) =ᶠ[𝓝 z] slitGreenTop := by
    filter_upwards [hZB,hZim] with w hw hwi
    exact (hform w hw hwi.1 hwi.2).symm
  rw [←InnerProductSpace.harmonicAt_congr_nhds hEq]
  exact ((analyticAt_const.mul (hPa z hzB)).sub analyticAt_const).harmonicAt_im

end SpringerLean
