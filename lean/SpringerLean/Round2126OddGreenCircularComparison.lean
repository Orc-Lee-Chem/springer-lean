import SpringerLean.Round2123StripMaximumAtFlatTop
import SpringerLean.Round2125OddGreenTopEdges

open Set Metric Real MeasureTheory

namespace SpringerLean

theorem clippedOddGreen_top_le_slit
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hK : IsConnected (exteriorOmitted F))
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (τ : ℝ) (hτ : 0 < τ)
    (w : ℂ) (hw₀ : 0 ≤ w.im) (hwπ : w.im ≤ π) :
    verticalPeriodicTop (clippedOddGreen F τ) (2*π) w ≤ slitGreenTop w := by
  let u := clippedOddGreen F τ
  let v := exteriorGreenCoordinate (slitMap 1) ∘ oddGreenChart
  let U := verticalPeriodicTop u (2*π)
  let V := slitGreenTop
  let Q : ℂ → ℝ := fun z => U z-V z
  let S : Set ℂ := {z | 0 ≤ z.im ∧ z.im ≤ π}
  let O : Set ℂ := {z | 0 < z.im ∧ z.im < π}
  have ho' : IsOpen O := (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)
  have hF' := slitMap_centeredExteriorUnivalent 1 (by simp)
  have hU := clippedOddGreen_continuous F hF τ
  have hV : Continuous v := (exteriorGreenCoordinate_continuous _ hF').comp (by unfold oddGreenChart; fun_prop)
  have hUc : ContinuousOn U S := by
    simpa only [S,U,show 2*π/2 = π by ring] using verticalPeriodicTop_continuousOn u hU
      (fun z => le_max_right _ _) (2*π) two_pi_pos (clippedOddGreen_periodic F hF ho τ)
  have hVc : ContinuousOn V S := slitGreenTop_continuousOn
  have hQc : ContinuousOn Q S := hUc.sub hVc
  have hQsub (z : ℂ) (hz₀ : 0 < z.im) (hzπ : z.im < π) :
      ∃ δ > 0, ∀ r > 0, r < δ → Q z ≤ circleAverage Q z r := by
    obtain ⟨d,hd,hu⟩ := clippedOddGreen_top_local_submean F hF ho τ hτ z.re z.im hz₀ hzπ
    obtain ⟨b,hb,hball⟩ := Metric.isOpen_iff.mp ho' z ⟨hz₀,hzπ⟩
    refine ⟨min d b,lt_min hd hb,?_⟩
    intro r hr hrd
    have hs : closedBall z |r| ⊆ O :=
      (closedBall_subset_ball (by rw [abs_of_pos hr]; exact hrd.trans_le (min_le_right _ _))).trans hball
    have hS : sphere z |r| ⊆ S := fun p hp =>
      let ht := hs (sphere_subset_closedBall hp)
      ⟨ht.1.le,ht.2.le⟩
    have hu' : U z ≤ circleAverage U z r := by
      simpa only [Complex.re_add_im] using hu r hr (hrd.trans_le (min_le_left _ _))
    have he : circleAverage V z r = V z := (slitGreenTop_harmonicOnNhd.mono hs).circleAverage_eq
    unfold Q
    rw [circleAverage_fun_sub ((hUc.mono hS).circleIntegrable') ((hVc.mono hS).circleIntegrable'),he]
    exact sub_le_sub_right hu' _
  change U w ≤ V w
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε/(1+π)
  have hη : 0 < η := div_pos hε (by positivity)
  let e := η/(2*π)
  have he : 0 < e := div_pos hη two_pi_pos
  have hpoint (z : ℂ) (hz : z ∈ S)
      (hb : ∀ t ∈ Ioc 0 (2*π), u ((z.re:ℂ)+(t:ℂ)*Complex.I) ≤ v ((z.re:ℂ)+(t:ℂ)*Complex.I)+e) :
      Q z ≤ η := by
    let f (t : ℝ) := u ((z.re:ℂ)+(t:ℂ)*Complex.I)
    let g (t : ℝ) := v ((z.re:ℂ)+(t:ℂ)*Complex.I)
    have hf := hU.comp (show Continuous (fun t : ℝ => (z.re:ℂ)+(t:ℂ)*Complex.I) by fun_prop)
    have hg := hV.comp (show Continuous (fun t : ℝ => (z.re:ℂ)+(t:ℂ)*Complex.I) by fun_prop)
    have h := periodicTopIntegral_le_add_of_forall_le_add f g hf hg (2*π) (2*z.im) e two_pi_pos
      (by linarith [hz.1]) (by linarith [hz.2]) (clippedOddGreen_periodic F hF ho τ z.re) he.le hb
    have hEq : (2*π)*e = η := by dsimp [e]; field_simp [pi_ne_zero]
    rw [hEq] at h
    change U z ≤ V z+η at h
    change U z-V z ≤ η
    linarith only [h]
  have h0 := zero_mem_exteriorOmitted_of_odd F hF ho
  have hG0 : exteriorGreenCoordinate F 0 = 0 := le_antisymm
    (le_of_not_gt (fun h => h0 ((exteriorGreenCoordinate_pos_iff F 0).mp h)))
    (exteriorGreenCoordinate_nonneg F 0)
  obtain ⟨d,hd,hnear⟩ := Metric.continuousAt_iff.mp (exteriorGreenCoordinate_continuous F hF).continuousAt e he
  obtain ⟨R,hR,hfar⟩ := exteriorGreenCoordinate_exists_far_log_bound F hF (e/2) (half_pos he)
  obtain ⟨R',hR',hfar'⟩ := exteriorGreenCoordinate_exists_far_log_bound (slitMap 1) hF' (e/2) (half_pos he)
  let a := min (w.re-1) (2*log d-2)
  let b := max (w.re+1) (2*log (max R R')+2)
  have ha : exp (a/2) < d := by
    rw [←Real.exp_log hd]
    apply Real.exp_lt_exp.mpr
    linarith [show a ≤ 2*log d-2 from min_le_right _ _]
  have hb : max R R' < exp (b/2) := by
    rw [←Real.exp_log (show 0 < max R R' from (by norm_num : (0:ℝ)<4).trans_le (hR.trans (le_max_left _ _)))]
    apply Real.exp_lt_exp.mpr
    linarith [show 2*log (max R R')+2 ≤ b from le_max_right _ _]
  let C := complexClosedRectangle a b 0 π
  have hCS : C ⊆ S := fun z hz => hz.2
  have hCw : w ∈ C := ⟨⟨by dsimp [a]; linarith [min_le_left (w.re-1) (2*log d-2)],
    by dsimp [b]; linarith [le_max_left (w.re+1) (2*log (max R R')+2)]⟩,hw₀,hwπ⟩
  have hedges (z : ℂ) (hz : z ∈ C) (hed : z.re = a ∨ z.re = b ∨ z.im = 0) : Q z ≤ η := by
    rcases hed with H | H | H
    · apply hpoint z (hCS hz)
      intro t _
      let y := oddGreenChart ((z.re:ℂ)+(t:ℂ)*Complex.I)
      have hy : dist y 0 < d := by rw [dist_zero_right,oddGreenChart_norm,H]; exact ha
      have hy' := hnear hy
      rw [hG0,Real.dist_eq,sub_zero,abs_of_nonneg (exteriorGreenCoordinate_nonneg F y)] at hy'
      change max (exteriorGreenCoordinate F y-τ) 0 ≤ exteriorGreenCoordinate (slitMap 1) y+e
      have hnonneg := exteriorGreenCoordinate_nonneg (slitMap 1) y
      exact max_le (by linarith only [hy',hτ,hnonneg]) (by linarith only [he,hnonneg])
    · apply hpoint z (hCS hz)
      intro t _
      let y := oddGreenChart ((z.re:ℂ)+(t:ℂ)*Complex.I)
      have hy : max R R' < ‖y‖ := by rw [oddGreenChart_norm,H]; exact hb
      have hf := abs_lt.mp (hfar y ((le_max_left _ _).trans_lt hy))
      have hv := abs_lt.mp (hfar' y ((le_max_right _ _).trans_lt hy))
      change max (exteriorGreenCoordinate F y-τ) 0 ≤ exteriorGreenCoordinate (slitMap 1) y+e
      exact max_le (by linarith [hf.2,hv.1]) (by linarith [exteriorGreenCoordinate_nonneg (slitMap 1) y])
    · have hu0 : U z = 0 := by
        unfold U verticalPeriodicTop
        rw [H,mul_zero]
        exact periodicTopIntegral_zero _ (hU.comp (by fun_prop)) _ two_pi_pos
          (clippedOddGreen_periodic F hF ho τ z.re)
      have hv0 : V z = 0 := by
        unfold V slitGreenTop verticalPeriodicTop
        rw [H,mul_zero]
        exact periodicTopIntegral_zero _ (hV.comp (by fun_prop)) _ two_pi_pos
          (oddGreenChart_potential_periodic _ hF' (fun z _ => slitMap_one_odd z) z.re)
      unfold Q
      rw [hu0,hv0,sub_zero]
      exact hη.le
  have htop (z : ℂ) (_ : z ∈ C) (hπz : z.im = π) :
      Q z ≤ η ∨ ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → Q z ≤ Q (z-(s:ℂ)*Complex.I) := by
    have heq : z = (z.re:ℂ)+(π:ℂ)*Complex.I := by rw [←hπz,Complex.re_add_im]
    by_cases hrad : ∀ y ∈ exteriorOmitted F, ‖y‖ ≤ exp (z.re/2)
    · left
      apply le_trans _ hη.le
      apply sub_nonpos.mpr
      convert clippedOddGreen_top_full_le_slit_of_radius_bound F hF ho τ hτ.le z.re hrad using 1
      · exact congrArg U heq
      · exact congrArg V heq
    · push_neg at hrad
      obtain ⟨y,hy,hy'⟩ := hrad
      obtain ⟨p,hp,hpn,_⟩ := exteriorGreenCoordinate_has_zero_on_radius F hK h0 y hy
        (exp (z.re/2)) (exp_pos _).le hy'.le
      obtain ⟨δ,hδ,hflat⟩ := clippedOddGreen_top_full_flat_of_omitted_on_radius F hF ho τ hτ z.re p hpn hp
      refine Or.inr ⟨min δ π,lt_min hδ pi_pos,?_⟩
      intro s hs hsδ
      have hsπ : s < π := hsδ.trans_le (min_le_right _ _)
      have heq' : z-(s:ℂ)*Complex.I = (z.re:ℂ)+((π-s:ℝ):ℂ)*Complex.I := by
        rw [Complex.ofReal_sub,sub_mul,←add_sub_assoc,←heq]
      unfold Q
      rw [heq',show U z = U ((z.re:ℂ)+(π:ℂ)*Complex.I) from congrArg U heq,
        show V z = V ((z.re:ℂ)+(π:ℂ)*Complex.I) from congrArg V heq]
      exact sub_le_sub (hflat s hs (hsδ.trans_le (min_le_left _ _)))
        (slitGreenTop_mono_height z.re (π-s) π (sub_nonneg.mpr hsπ.le) (sub_le_self _ hs.le) le_rfl)
  have hW := strip_le_of_local_submean_and_flat_top Q a b η hη (hQc.mono hCS) hQsub hedges htop w hCw
  have hE : η*(1+π) = ε := div_mul_cancel₀ _ (by positivity)
  rw [hE] at hW
  change U w-V w ≤ ε at hW
  linarith only [hW]

/-- The actual Green circular means of an odd normalized exterior map
with connected omitted set are bounded by those of the slit. -/
theorem oddExteriorGreen_circleAverage_le_slitMap_one
    (F : ℂ → ℂ) (hF : CenteredExteriorUnivalent F) (hK : IsConnected (exteriorOmitted F))
    (ho : ∀ z ∈ exteriorDisk, F (-z) = -F z) (r : ℝ) (hr : 0 < r) :
    circleAverage (exteriorGreenCoordinate F) 0 r ≤
      circleAverage (exteriorGreenCoordinate (slitMap 1)) 0 r := by
  let x := 2*log r
  have hx : exp (x/2) = r := by rw [show x/2 = log r by dsimp [x]; ring,Real.exp_log hr]
  let f (t : ℝ) := exteriorGreenCoordinate F (oddGreenChart ((x:ℂ)+(t:ℂ)*Complex.I))
  have hf : Continuous f := (exteriorGreenCoordinate_continuous F hF).comp (by unfold oddGreenChart; fun_prop)
  have hfp := oddGreenChart_potential_periodic F hF ho x
  have heq : periodicTopIntegral f (2*π) (2*π) = (2*π)*circleAverage (exteriorGreenCoordinate F) 0 r := by
    rw [periodicTopIntegral_full_of_nonneg f hf _ two_pi_pos hfp (fun _ => exteriorGreenCoordinate_nonneg _ _) (-π),
      show -π+2*π = π by ring]
    exact (oddGreenChart_integral_eq_circleAverage F hF ho x).trans (by rw [hx])
  have hS : slitGreenTop ((x:ℂ)+(π:ℂ)*Complex.I) =
      (2*π)*circleAverage (exteriorGreenCoordinate (slitMap 1)) 0 r := by
    rw [slitGreenTop_eq_arc x π pi_pos.le le_rfl,oddGreenChart_integral_eq_circleAverage (slitMap 1)
      (slitMap_centeredExteriorUnivalent 1 (by simp)) (fun z _ => slitMap_one_odd z),hx]
  apply le_of_forall_pos_le_add
  intro ε hε
  let t := ε/2
  let g (θ : ℝ) := clippedOddGreen F t ((x:ℂ)+(θ:ℂ)*Complex.I)
  have hg := (clippedOddGreen_continuous F hF t).comp
    (show Continuous (fun θ : ℝ => (x:ℂ)+(θ:ℂ)*Complex.I) by fun_prop)
  have hlo := periodicTopIntegral_le_add_of_forall_le_add f g hf hg (2*π) (2*π) t two_pi_pos
    two_pi_pos.le le_rfl hfp (half_pos hε).le (fun θ _ => by
      have h : f θ-t ≤ g θ := le_max_left _ _
      linarith only [h])
  have h := clippedOddGreen_top_le_slit F hF hK ho t (half_pos hε) ((x:ℂ)+(π:ℂ)*Complex.I)
    (by simp [Complex.add_im,Complex.mul_im,pi_pos.le]) (by simp [Complex.add_im,Complex.mul_im])
  change verticalPeriodicTop (clippedOddGreen F t) (2*π) ((x:ℂ)+(π:ℂ)*Complex.I) ≤ _ at h
  unfold verticalPeriodicTop at h
  simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,sub_zero,add_zero,zero_add] at h
  change periodicTopIntegral g (2*π) (2*π) ≤ _ at h
  rw [heq] at hlo
  rw [hS] at h
  apply le_of_mul_le_mul_left ?_ two_pi_pos
  have hε' : 0 ≤ (2*π)*(ε-t) := mul_nonneg two_pi_pos.le (by dsimp [t]; linarith)
  nlinarith only [hlo,h,hε']

end SpringerLean
