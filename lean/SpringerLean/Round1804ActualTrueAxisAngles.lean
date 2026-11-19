import SpringerLean.Round1785ActualAlignedNearPhaseCost

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 800000

theorem trueAxis_strip_cost_coarse
    {y Q s x H : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) (hs : 0 ≤ s)
    (hx : (9/5 : ℝ) ≤ x) (hH : H*x=Q)
    (hstrip : Q^2 ≤ 4*y*(y+2*s)) : H^2/2 ≤ 1/6+(5/8 : ℝ)*s := by
  have hys := mul_le_mul_of_nonneg_right hy1 hs
  have hy2 : y^2 ≤ 1/4 := by nlinarith
  have hQ : Q^2 ≤ 1+4*s := by nlinarith
  have hx2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9/5) hx 2
  have hsq := congrArg (fun z : ℝ => z^2) hH
  simp only [mul_pow] at hsq
  have hh := mul_le_mul_of_nonneg_right hx2 (sq_nonneg H)
  nlinarith

theorem exteriorOmitted_actualEndpoint_trueAxis_angles
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (z : ℂ) (hz : ‖z‖ < 1)
    (hx : (9/5 : ℝ) ≤ (conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let u := conj (P/(‖P‖ : ℂ))*actualHarmonic F z
    let s := m*(1-u.re/2)
    let h := |u.im|/u.re
    m^2*h^2/2 ≤ 1/6+(5/8 : ℝ)*s ∧
      (s ≤ 2 → |(k : ℝ)*Complex.arg u| ≤ 6/7) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let W := exteriorFineEndpointWidth P
  let ξ := P/(‖P‖ : ℂ)
  let u := conj ξ*actualHarmonic F z
  let s := m*(1-u.re/2)
  let H := m*|u.im|/u.re
  have hm : (1500 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hW0 : 0 ≤ W := by dsimp [W, exteriorFineEndpointWidth]; positivity
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have hu0 : 0 < u.re := by dsimp [u, ξ]; linarith
  have hnorm : ‖u‖=‖actualHarmonic F z‖ := by dsimp [u]; rw [norm_mul, Complex.norm_conj, hξ, one_mul]
  have hu2 : u.re ≤ 2 := by
    calc
      u.re ≤ ‖u‖ := Complex.re_le_norm _
      _ = ‖actualHarmonic F z‖ := hnorm
      _ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc (actualHarmonic_mem_convexHull_omitted F hc hz)
  have hs0 : 0 ≤ s := mul_nonneg hm0.le (by linarith)
  have hy0 : 0 ≤ m*W := mul_nonneg hm0.le hW0
  have hstrip := (exteriorOmitted_actualEndpoint_fine_strip F hc k hk P hP hd ht
    (actualHarmonic F z) (actualHarmonic_mem_convexHull_omitted F hc hz)).2.1
  have hquad := rotated_strip_scaled_quadratic hm0.le hW0 (exteriorOmitted_norm_le_two F hc hP)
    hu0.le (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ))
    (by norm_num : (1 : ℝ)*0=|0|) (by simp : u.re=1*u.re+0*u.im) hstrip
  simp only [mul_zero, add_zero] at hquad
  have hHid : H*u.re=m*|u.im| := by dsimp [H]; exact div_mul_cancel₀ _ hu0.ne'
  have hcost := trueAxis_strip_cost_coarse hy0 hW.le hs0 hx hHid hquad
  have hcost' : m^2*(|u.im|/u.re)^2/2 ≤ 1/6+(5/8 : ℝ)*s := by
    convert hcost using 1 <;> dsimp [H] <;> ring
  refine ⟨hcost', ?_⟩
  intro hs2
  change s ≤ 2 at hs2
  have hH2 : H^2 ≤ 17/6 := by linarith
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hHshort : (501/1000 : ℝ)*H < 6/7 := by
    by_contra hh
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6/7) (le_of_not_gt hh) 2
    nlinarith
  have hmk : (k : ℝ) ≤ (501/1000 : ℝ)*m := by
    have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
    have heq : m=2*(k : ℝ)-2 := by
      dsimp [m]
      rw [Nat.cast_sub (by omega : 2 ≤ 2*k), Nat.cast_mul, Nat.cast_ofNat]
    rw [heq]
    linarith
  have harg := mul_le_mul_of_nonneg_left (complex_arg_abs_le_slope hu0) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hscale : (k : ℝ)*H/m ≤ (501/1000 : ℝ)*H := by
    apply (div_le_iff₀ hm0).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmk hH0]
  have heq : (k : ℝ)*H/m=(k : ℝ)*(|u.im|/u.re) := by
    dsimp [H]
    field_simp
  rw [heq] at hscale
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  exact harg.trans (hscale.trans hHshort.le)

end SpringerLean

#print axioms SpringerLean.exteriorOmitted_actualEndpoint_trueAxis_angles
