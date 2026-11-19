import SpringerLean.Round2000OddStarMovingBoundaryPoint
import Mathlib.Analysis.InnerProductSpace.Calculus

namespace SpringerLean
open scoped RealInnerProductSpace

/-- A reusable real-parameter logarithmic-distance derivative for
a nonvanishing complex path. -/
theorem log_norm_hasDerivAt_of_nonzero
    (f : ℝ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (h0 : f 0 ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log ‖f t‖)
      (⟪f 0, f'⟫ / ‖f 0‖ ^ 2) 0 := by
  have hsq : HasDerivAt (fun t : ℝ => ‖f t‖ ^ 2)
      (2 * ⟪f 0, f'⟫) 0 := hf.norm_sq
  have hsqne : ‖f 0‖ ^ 2 ≠ 0 := by
    simp [h0]
  have hlog := hsq.log hsqne
  have hhalf := hlog.const_mul ((1 / 2 : ℝ))
  convert hhalf using 1
  · funext t
    rw [Real.log_pow]
    ring
  · ring

theorem oddStarTipRadius_zero_pos (m : ℕ) :
    0 < oddStarTipRadius m 0 := by
  unfold oddStarTipRadius
  norm_num
  positivity

theorem oddStarOppositeTip_nonzero_at_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 -
      (oddStarTipRadius m 0 : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I) ≠ 0 := by
  let δ : ℝ := Real.pi - Real.pi / (m : ℝ)
  have hsin : 0 < Real.sin δ :=
    (oddStar_opposite_tip_angle_geometry m hm 0 0 (le_refl _) (le_refl _)).1
  have hR : 0 < oddStarTipRadius m 0 := oddStarTipRadius_zero_pos m
  have hηim : (Complex.exp ((δ : ℂ) * Complex.I)).im = Real.sin δ := by
    rw [Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hZ : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 =
      (oddStarBoundaryRadius m θ : ℂ) := by
    simp [oddStarMovingBoundaryPoint, oddStarBoundaryFactor]
  intro hzero
  have him := congrArg Complex.im hzero
  rw [hZ] at him
  have hηim' :
      (Complex.exp ((↑Real.pi - ↑Real.pi / (m : ℂ)) * Complex.I)).im =
        Real.sin δ := by
    convert hηim using 1 <;> simp [δ]
  rcases (by simpa only [Complex.sub_im, Complex.ofReal_im, zero_sub,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, zero_add, Complex.zero_im] using him) with h
  simp [hηim'] at h
  rcases h with h | h
  · linarith
  · linarith

/-- Logarithmic distance from the moving boundary point to the
opposite moving tip in the explicit odd-star variation. -/
noncomputable def oddStarOppositeTipLogDistance (m : ℕ) (θ t : ℝ) : ℝ :=
  Real.log ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
    (oddStarTipRadius m t : ℂ) *
      Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖

theorem oddStarOppositeTipLogDistance_hasDerivAt_zero
    (m : ℕ) (hm : 3 ≤ m) (θ : ℝ) :
    HasDerivAt (oddStarOppositeTipLogDistance m θ)
      (⟪oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 -
          (oddStarTipRadius m 0 : ℂ) *
            Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I),
        (oddStarBoundaryRadius m θ : ℂ) * (m : ℂ)⁻¹ *
          ((Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I)⟫ /
        ‖oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 -
          (oddStarTipRadius m 0 : ℂ) *
            Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)‖ ^ 2) 0 := by
  let η : ℂ := Complex.exp (((Real.pi - Real.pi / (m : ℝ)) : ℝ) * Complex.I)
  let f : ℝ → ℂ := fun t =>
    oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ t -
      (oddStarTipRadius m t : ℂ) * η
  have hZ := oddStarMovingBoundaryPoint_actualRadius_hasDerivAt_zero m θ
  have hR : HasDerivAt
      (fun t : ℝ => (oddStarTipRadius m t : ℂ)) 0 0 := by
    simpa using (oddStarTipRadius_hasDerivAt_zero m hm).ofReal_comp
  have hf : HasDerivAt f
      ((oddStarBoundaryRadius m θ : ℂ) * (m : ℂ)⁻¹ *
        ((Real.sin θ : ℂ) + (Real.cos θ - 1 : ℝ) * Complex.I)) 0 := by
    convert hZ.sub (hR.mul_const η) using 1 <;> simp [f]
  have hne : f 0 ≠ 0 := oddStarOppositeTip_nonzero_at_zero m hm θ
  exact log_norm_hasDerivAt_of_nonzero f _ hf hne

end SpringerLean

#print axioms SpringerLean.oddStarOppositeTipLogDistance_hasDerivAt_zero
