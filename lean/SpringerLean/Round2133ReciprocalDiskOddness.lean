import SpringerLean.Round2132ReciprocalRotation

open Set Metric Function

namespace SpringerLean

/-- A disk uniformization fixing the origin is odd when the reciprocal
image is centrally symmetric. This uses the exact Schwarz equality
case for the induced involution. -/
theorem reciprocalDiskUniformization_odd
    (K : Set ℂ) (a : ℂ) (f : ReciprocalDiskUniformization K a)
    (hSym : ∀ z ∈ reciprocalExteriorDomain K a, -z ∈ reciprocalExteriorDomain K a) :
    ∀ z ∈ ball (0:ℂ) 1, f.toFun (-z) = -f.toFun z := by
  let U := reciprocalExteriorDomain K a
  let D := ball (0:ℂ) 1
  let g := invFunOn f.toFun D
  let A := fun z : ℂ => g (-f.toFun z)
  have hIm : f.toFun '' D = U := f.bijective.image_eq
  have hNeg (z : ℂ) (hz : z ∈ D) : -f.toFun z ∈ f.toFun '' D := by
    rw [hIm]
    exact hSym _ (f.bijective.1 hz)
  have hAin : MapsTo A D D := fun z hz => invFunOn_mem (hNeg z hz)
  have hAg (z : ℂ) (hz : z ∈ D) : f.toFun (A z) = -f.toFun z :=
    invFunOn_eq (hNeg z hz)
  have hgd : DifferentiableOn ℂ g U := fun z hz =>
    (reciprocalDiskUniformization_inverse_analyticAt f z hz).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ A D := hgd.comp f.differentiable.neg
    (fun z hz => hSym _ (f.bijective.1 hz))
  have h0D : (0:ℂ) ∈ D := mem_ball_self zero_lt_one
  have h0 : A 0 = 0 := by
    change g (-f.toFun 0) = 0
    rw [f.map_zero,neg_zero]
    have h := f.bijective.2.1.leftInvOn_invFunOn h0D
    simpa only [f.map_zero] using h
  have hInv (z : ℂ) (hz : z ∈ D) : A (A z) = z := by
    change g (-f.toFun (A z)) = z
    rw [hAg z hz,neg_neg]
    exact f.bijective.2.1.leftInvOn_invFunOn hz
  have hn (z : ℂ) (hz : z ∈ D) : ‖A z‖ = ‖z‖ := by
    have hle (w : ℂ) (hw : w ∈ D) : ‖A w‖ ≤ ‖w‖ :=
      Complex.norm_le_norm_of_mapsTo_ball hd
        (fun t ht => ball_subset_closedBall (hAin ht)) h0 (mem_ball_zero_iff.mp hw)
    have h := hle (A z) (hAin hz)
    rw [hInv z hz] at h
    exact le_antisymm (hle z hz) h
  let z₀ : ℂ := 1/2
  have hzD : z₀ ∈ D := by
    change z₀ ∈ ball (0:ℂ) 1
    rw [mem_ball,dist_zero_right]
    norm_num [z₀,norm_div]
  have hz0 : z₀ ≠ 0 := by norm_num [z₀]
  let c := dslope A 0 z₀
  have hc : ‖c‖ = 1 := by
    dsimp [c]
    rw [dslope_of_ne A hz0,slope_def_field,h0,sub_zero,sub_zero,norm_div,hn z₀ hzD,
      div_self (norm_ne_zero_iff.mpr hz0)]
  have hmaps : MapsTo A D (closedBall (A 0) 1) := by
    rw [h0]
    exact fun z hz => ball_subset_closedBall (hAin hz)
  have hlinear (z : ℂ) (hz : z ∈ D) : A z = z*c := by
    have h := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hd hmaps hzD (by simpa only [div_one] using hc)
    simpa only [h0,sub_zero,smul_eq_mul,zero_add] using h hz
  have hcsq : c^2 = 1 := by
    have h := hInv z₀ hzD
    rw [hlinear (A z₀) (hAin hzD),hlinear z₀ hzD] at h
    have he : z₀*c^2=z₀ := by simpa only [pow_two,mul_assoc] using h
    exact mul_left_cancel₀ hz0 (he.trans (mul_one _).symm)
  have hcn : c = -1 := by
    rcases sq_eq_one_iff.mp hcsq with h | h
    · have hfix : A z₀ = z₀ := by rw [hlinear z₀ hzD,h,mul_one]
      have he := hAg z₀ hzD
      rw [hfix] at he
      have hf0 : f.toFun z₀ = 0 := by linear_combination he/2
      exact (hz0 (f.bijective.2.1 hzD h0D (hf0.trans f.map_zero.symm))).elim
    · exact h
  intro z hz
  have hAZ : A z = -z := by rw [hlinear z hz,hcn,mul_neg_one]
  rw [←hAZ]
  exact hAg z hz

end SpringerLean
