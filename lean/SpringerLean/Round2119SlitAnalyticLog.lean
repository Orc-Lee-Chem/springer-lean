import SpringerLean.Round2113SlitTopArc

open Set Real

namespace SpringerLean

private theorem slitMap_one_im (w : ℂ) : (slitMap 1 w).im = w.im*(1-(Complex.normSq w)⁻¹) := by
  simp only [slitMap,one_div,Complex.add_im,Complex.inv_im]
  ring

private theorem slitMap_one_re (w : ℂ) : (slitMap 1 w).re = w.re*(1+(Complex.normSq w)⁻¹) := by
  simp only [slitMap,one_div,Complex.add_re,Complex.inv_re]
  ring

theorem slitMap_one_upperHalfPlane_mem_image (z : ℂ) (hz : 0 < z.im) :
    z ∈ slitMap 1 '' exteriorDisk := by
  by_contra h
  have hh : z ∈ (slitMap 1 '' exteriorDisk)ᶜ := h
  rw [slitMap_one_omitted_eq_segment] at hh
  exact hz.ne' hh.1

theorem slitMap_one_inverse_im_pos (z : ℂ) (h : 0 < z.im) :
    0 < (exteriorInverse (slitMap 1) z).im := by
  let w := exteriorInverse (slitMap 1) z
  have hw : 1 < ‖w‖ := Function.invFunOn_mem (slitMap_one_upperHalfPlane_mem_image z h)
  have he : slitMap 1 w = z := Function.invFunOn_eq (slitMap_one_upperHalfPlane_mem_image z h)
  have hsq : 1 < Complex.normSq w := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have hh : 0 < 1-(Complex.normSq w)⁻¹ :=
    sub_pos.mpr ((inv_lt_one₀ (zero_lt_one.trans hsq)).mpr hsq)
  have hp : 0 < (slitMap 1 w).im := by rwa [he]
  rw [slitMap_one_im] at hp
  exact pos_of_mul_pos_left hp hh.le

/-- The inverse logarithm is holomorphic on the chart of the upper
half-plane. Multiplying by `-I` places its argument in the right
half-plane and makes it real on the center line. -/
noncomputable def slitGreenAnalyticLog (z : ℂ) : ℂ :=
  Complex.log (-Complex.I * exteriorInverse (slitMap 1) (oddGreenChart z))

def oddGreenOpenStrip : Set ℂ := {z | -π < z.im ∧ z.im < π}

private theorem oddGreenChart_im_pos_of_strip (z : ℂ) (hz : z ∈ oddGreenOpenStrip) :
    0 < (oddGreenChart z).im := by
  have h := oddGreenChart_im_pos z.re z.im hz.1 hz.2
  simpa only [Complex.re_add_im] using h

theorem slitGreenAnalyticLog_analyticOnNhd : AnalyticOnNhd ℂ slitGreenAnalyticLog oddGreenOpenStrip := by
  intro z hz
  let w := oddGreenChart z
  have him := oddGreenChart_im_pos_of_strip z hz
  have hv := slitMap_one_upperHalfPlane_mem_image w him
  have hi : AnalyticAt ℂ (exteriorInverse (slitMap 1)) w := by
    obtain ⟨v,hv,he⟩ := hv
    change slitMap 1 v = w at he
    exact he ▸ exteriorInverse_analyticAt_image (slitMap 1)
      (slitMap_centeredExteriorUnivalent 1 (by simp)) v hv
  have hc : AnalyticAt ℂ (fun u => exteriorInverse (slitMap 1) (oddGreenChart u)) z :=
    hi.comp (f := oddGreenChart) (x := z) (oddGreenChart_analyticOnNhd z (mem_univ z))
  have ha : AnalyticAt ℂ (fun u => -Complex.I * exteriorInverse (slitMap 1) (oddGreenChart u)) z :=
    analyticAt_const.mul hc
  apply ha.clog
  apply Or.inl
  simpa [Complex.mul_re] using slitMap_one_inverse_im_pos w him

theorem slitGreenAnalyticLog_re (z : ℂ) (hz : z ∈ oddGreenOpenStrip) :
    (slitGreenAnalyticLog z).re = exteriorGreenCoordinate (slitMap 1) (oddGreenChart z) := by
  classical
  have hm := slitMap_one_upperHalfPlane_mem_image _ (oddGreenChart_im_pos_of_strip z hz)
  rw [slitGreenAnalyticLog,Complex.log_re,norm_mul,norm_neg,Complex.norm_I,one_mul,
    exteriorGreenCoordinate,if_pos hm]

theorem slitGreenAnalyticLog_im_real (x : ℝ) : (slitGreenAnalyticLog (x:ℂ)).im = 0 := by
  let w := oddGreenChart (x:ℂ)
  let v := exteriorInverse (slitMap 1) w
  have hz : (x:ℂ) ∈ oddGreenOpenStrip := by
    change -π < 0 ∧ 0 < π
    exact ⟨neg_neg_of_pos pi_pos,pi_pos⟩
  have hw := oddGreenChart_im_pos_of_strip _ hz
  have hvi : 0 < v.im := slitMap_one_inverse_im_pos w hw
  have hwr : w.re = 0 := by
    have h := oddGreenChart_abs_re x 0 (by simp [pi_pos.le])
    have h' : |w.re| = 0 := by simpa [w] using h
    exact abs_eq_zero.mp h'
  have hv : slitMap 1 v = w := Function.invFunOn_eq (slitMap_one_upperHalfPlane_mem_image w hw)
  have hvr : v.re = 0 := by
    have h := congrArg Complex.re hv
    rw [slitMap_one_re,hwr] at h
    exact (mul_eq_zero.mp h).resolve_right
      (add_pos_of_pos_of_nonneg zero_lt_one (inv_nonneg.mpr (Complex.normSq_nonneg v))).ne'
  have he : -Complex.I*v = (v.im:ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,hvr]
  change (Complex.log (-Complex.I*v)).im = 0
  rw [he,Complex.log_im,Complex.arg_ofReal_of_nonneg hvi.le]

end SpringerLean
