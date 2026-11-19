import SpringerLean.Round1833ActualDeficitTransverseBound

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 1300000

/-- The outer cone uses a center proportional to sqrt(d log(2/d));
its radius vanishes even for arbitrarily small positive deficits. -/
theorem unit_perturbed_axis_tiny_outer_cone
    (k : ℕ) (hk : 751 ≤ k) {E : ℝ} (hE : 0 < E)
    (ξ v w : ℂ) (hξ : ‖ξ‖=1) (hvunit : ‖v‖=1)
    (δ : ℝ) (hv : v=ξ*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |δ| ≤ Real.pi/(2*(k : ℝ)))
    (hforward : 0 ≤ (conj ξ*w).re)
    (htrans : |(conj ξ*w).im| ≤ (5/2 : ℝ)*Real.sqrt E)
    (houter : 6*(k : ℝ)*Real.sqrt E < ‖w‖) :
    ∃ θ : ℝ, w=v*(‖w‖ : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) ∧
      |(k : ℝ)*θ| ≤ 14/5 ∧ 0 < (conj v*w).re := by
  let u := conj ξ*w
  let r := ‖w‖
  have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hroot : 0 < Real.sqrt E := Real.sqrt_pos.mpr hE
  have hnorm : ‖u‖=r := by dsimp [u,r]; rw [norm_mul,Complex.norm_conj,hξ,one_mul]
  have hnorm2 : r^2=u.re^2+u.im^2 := by
    rw [←hnorm,Complex.sq_norm]
    simp only [Complex.normSq_apply,pow_two]
  have hr0 : 0 < r := (show 0 < 6*(k : ℝ)*Real.sqrt E by positivity).trans houter
  have hq2 : u.im^2 ≤ (25/4 : ℝ)*E := by
    have hh := pow_le_pow_left₀ (abs_nonneg (conj ξ*w).im) htrans 2
    rw [sq_abs,mul_pow,Real.sq_sqrt hE.le] at hh
    nlinarith [hh]
  have hr6 : 6*Real.sqrt E < r := by
    change 6*(k : ℝ)*Real.sqrt E < r at houter
    have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ k by linarith) hroot.le
    nlinarith
  have hp : r/2 < u.re := by
    change 0 ≤ u.re at hforward
    have hh := pow_lt_pow_left₀ hr6 (by positivity : 0 ≤ 6*Real.sqrt E) (by norm_num : 2 ≠ 0)
    rw [mul_pow,Real.sq_sqrt hE.le] at hh
    nlinarith
  have hp0 : 0 < u.re := by linarith
  have hslope : (k : ℝ)*(|u.im|/u.re) ≤ 5/6 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hp0).mpr
    have hh := mul_le_mul_of_nonneg_left htrans hk0.le
    change 6*(k : ℝ)*Real.sqrt E < r at houter
    change (k : ℝ)*|u.im| ≤ (k : ℝ)*((5/2 : ℝ)*Real.sqrt E) at hh
    nlinarith
  have harg := complex_arg_abs_le_slope hp0
  have hargk : |(k : ℝ)*Complex.arg u| ≤ 5/6 := by
    rw [abs_mul,abs_of_pos hk0]
    exact (mul_le_mul_of_nonneg_left harg hk0.le).trans hslope
  have hδk : |(k : ℝ)*δ| ≤ Real.pi/2 := by
    rw [abs_mul,abs_of_pos hk0]
    have hh := (le_div_iff₀ (show (0 : ℝ) < 2*(k : ℝ) by positivity)).mp hδ
    nlinarith
  let θ := Complex.arg u-δ
  have hθ : |(k : ℝ)*θ| ≤ 14/5 := by
    have hh := abs_sub_le ((k : ℝ)*Complex.arg u) 0 ((k : ℝ)*δ)
    simp only [sub_zero,zero_sub,abs_neg] at hh
    dsimp [θ]
    rw [mul_sub]
    linarith [Real.pi_lt_d2]
  have hpolar := unit_direction_polar ξ w hξ
  have hw : w=v*(‖w‖ : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
    have he : Complex.exp ((δ : ℂ)*Complex.I)*Complex.exp ((θ : ℂ)*Complex.I)=
        Complex.exp ((Complex.arg u : ℂ)*Complex.I) := by
      rw [←Complex.exp_add]
      congr 1
      dsimp [θ]
      push_cast
      ring
    rw [hv]
    calc
      w = ξ*(‖w‖ : ℂ)*Complex.exp ((Complex.arg u : ℂ)*Complex.I) := hpolar
      _ = _ := by rw [←he]; ring
  have hθ1 : |θ| ≤ 1 := by
    rw [abs_mul,abs_of_pos hk0] at hθ
    nlinarith [abs_nonneg θ]
  have hcos : 0 < Real.cos θ := by
    have hs := pow_le_pow_left₀ (abs_nonneg θ) hθ1 2
    rw [sq_abs] at hs
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hproj : (conj v*w).re=r*Real.cos θ := by
    have hvv : conj v*v=1 := by simp [RCLike.conj_mul,hvunit]
    have heq : conj v*w=(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by
      rw [hw]
      calc
        _ = (conj v*v)*(r : ℂ)*Complex.exp ((θ : ℂ)*Complex.I) := by ring
        _ = _ := by rw [hvv,one_mul]
    rw [heq]
    simp [Complex.exp_mul_I,Complex.mul_re,←Complex.ofReal_cos,←Complex.ofReal_sin]
  exact ⟨θ,hw,hθ,by rw [hproj]; exact mul_pos hr0 hcos⟩

end SpringerLean

#print axioms SpringerLean.unit_perturbed_axis_tiny_outer_cone
