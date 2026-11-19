import SpringerLean.Round1784ActualAlignedStripCoordinates
import SpringerLean.Round1778AlignedComplexPhaseCost

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 700000

theorem complex_arg_abs_le_slope {u : ℂ} (hu : 0 < u.re) :
    |Complex.arg u| ≤ |u.im|/u.re := by
  have ha := (Complex.abs_arg_lt_pi_div_two_iff).mpr (Or.inl hu)
  have hrange := abs_lt.mp ha
  have heq : Complex.arg u=Real.arctan (u.im/u.re) := by
    rw [←Complex.tan_arg u, Real.arctan_tan hrange.1 hrange.2]
  rw [heq]
  simpa only [abs_div, abs_of_pos hu] using
    (Real.abs_arctan_le_abs (x := u.im/u.re))

theorem unit_direction_polar (v w : ℂ) (hv : ‖v‖=1) :
    w=v*(‖w‖ : ℂ)*Complex.exp ((Complex.arg (conj v*w) : ℂ)*Complex.I) := by
  have hnorm : ‖conj v*w‖=‖w‖ := by rw [norm_mul, Complex.norm_conj, hv, one_mul]
  have hvv : v*conj v=1 := by
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
  have hp := Complex.norm_mul_exp_arg_mul_I (conj v*w)
  rw [hnorm] at hp
  calc
    w=v*(conj v*w) := by rw [←mul_assoc, hvv, one_mul]
    _ = v*((‖w‖ : ℂ)*Complex.exp ((Complex.arg (conj v*w) : ℂ)*Complex.I)) :=
      congrArg (fun u : ℂ => v*u) hp.symm
    _ = _ := by ring

/-- The actual strip now discharges the angular-cone hypothesis in
the aligned near subregion. This is pointwise on the actual filling,
not a scalar test conditional on an unproved cone estimate. -/
theorem actualSignedPhaseDensity_aligned_near_le_projection
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (z : ℂ) (hz : ‖z‖ < 1) (hx : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (a : ℝ) (hay : a*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P) ≤ 3)
    (hs : ((2*k-2 : ℕ) : ℝ)*(1-(conj v*actualHarmonic F z).re/2) ≤ 7*a/5) :
    actualSignedPhaseDensity F k beta z ≤
      (max ((conj v*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let w := actualHarmonic F z
  let u := conj v*w
  let H := m*|u.im|/u.re
  have hx0 : 0 < u.re := by dsimp [u, w]; linarith
  obtain ⟨hy0, hy1, hQ0, hs0, hH0, hquad, hslope⟩ :=
    exteriorOmitted_actualEndpoint_aligned_scaled_strip F hc k hk P hP hd ht hW v δ hv hδ
      w (actualHarmonic_mem_convexHull_omitted F hc hz) hx
  have hnear := aligned_strip_near_angle hk hy0 hQ0 hH0 hquad hs hay hslope
  have hm0 : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < 2*k-2)
  have hrewrite : (k : ℝ)*H/m=(k : ℝ)*(|u.im|/u.re) := by
    dsimp [H]
    field_simp
  change (k : ℝ)*H/m < 14/5 at hnear
  rw [hrewrite] at hnear
  have harg := mul_le_mul_of_nonneg_left (complex_arg_abs_le_slope hx0) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hangle : |(k : ℝ)*Complex.arg u| ≤ 14/5 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact harg.trans hnear.le
  have hnorm : ‖u‖=‖w‖ := by dsimp [u]; rw [norm_mul, Complex.norm_conj, hvunit, one_mul]
  have hwpos : 0 < ‖w‖ := by
    have hh := Complex.re_le_norm u
    rw [hnorm] at hh
    exact hx0.trans_le hh
  exact actualSignedPhaseDensity_le_projected_of_aligned_polar F beta v z hvunit k hk
    hphase hwpos (unit_direction_polar v w hvunit) hangle hx0.le

end SpringerLean

#print axioms SpringerLean.actualSignedPhaseDensity_aligned_near_le_projection
