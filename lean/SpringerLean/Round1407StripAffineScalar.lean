import SpringerLean.Round1406SelectedTwoWidths

namespace SpringerLean

/-- A small squared strip width pays the affine radial correction on
the positive projection half. The plateau covers the lower projection
range; the active branch uses only a short scalar square comparison. -/
theorem smallStrip_affinePlatform_radius_cap
    {x R W v : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2)
    (hR : R ≤ 2)
    (hW0 : 0 ≤ W) (hW : W ≤ 1/100)
    (hv0 : 0 ≤ v)
    (hvstrip : v^2 ≤ (x-2*W)^2+4*W*R) :
    v ≤ max (19/10 : ℝ)
      (2-(1-(107/100 : ℝ)*W)*(2-x)+(107/100 : ℝ)*W^2) := by
  have hRw : 4*W*R ≤ 8*W := by
    have h := mul_le_mul_of_nonneg_left hR (by nlinarith : 0 ≤ 4*W)
    nlinarith
  by_cases hlow : x ≤ (949/500 : ℝ)
  · have hprod : 0 ≤ ((949/500 : ℝ)-x)*((949/500 : ℝ)+x-4*W) :=
      mul_nonneg (by linarith) (by linarith)
    have hWsq : W^2 ≤ W/100 := by
      have h := mul_nonneg hW0 (by linarith : 0 ≤ (1/100 : ℝ)-W)
      nlinarith
    have hcap : (x-2*W)^2+4*W*R ≤ (19/10 : ℝ)^2 := by
      nlinarith [hprod,hWsq]
    have hv : v ≤ (19/10 : ℝ) :=
      (sq_le_sq₀ hv0 (by norm_num)).mp (hvstrip.trans hcap)
    exact hv.trans (le_max_left _ _)
  · have hx : (949/500 : ℝ) ≤ x := le_of_lt (lt_of_not_ge hlow)
    let z : ℝ := W*(2-x+W)
    have hz : 0 ≤ z := mul_nonneg hW0 (by linarith)
    have hcoeff : 0 ≤ (107/50 : ℝ)*x-4 := by linarith
    have hmul := mul_nonneg hcoeff hz
    have hq : (x-2*W)^2+4*W*R ≤ x^2+4*z := by
      dsimp [z]
      nlinarith [hRw]
    let a : ℝ := x+(107/100 : ℝ)*z
    have ha0 : 0 ≤ a := by dsimp [a]; nlinarith
    have ha2 : x^2+4*z ≤ a^2 := by
      dsimp [a]
      nlinarith [hmul, sq_nonneg ((107/100 : ℝ)*z)]
    have hv : v ≤ a :=
      (sq_le_sq₀ hv0 ha0).mp (hvstrip.trans (hq.trans ha2))
    have hae : a = 2-(1-(107/100 : ℝ)*W)*(2-x)+(107/100 : ℝ)*W^2 := by
      dsimp [a,z]
      ring
    rw [hae] at hv
    exact hv.trans (le_max_right _ _)

end SpringerLean

#print axioms SpringerLean.smallStrip_affinePlatform_radius_cap
