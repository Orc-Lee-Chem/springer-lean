import SpringerLean.Round1786FarPowerRatio

open scoped ComplexConjugate

namespace SpringerLean
set_option maxHeartbeats 800000

/-- Polar factorization using only real projection and transverse
slope, followed by the far-region logarithmic budget. -/
theorem far_complex_power_le_lower_test
    (N : ℕ) (hN : 4 ≤ N) (v w : ℂ) (hv : ‖v‖=1)
    {a s : ℝ} (ha : 0 ≤ a) (has : a ≤ s) (hs : s < 2*(N : ℝ))
    (hx : 0 < (conj v*w).re)
    (hxs : (conj v*w).re=2*(1-s/(2*(N : ℝ))))
    (hcost : (2*(N : ℝ))^2*(|(conj v*w).im|/(conj v*w).re)^2/2 < 8*(s-a)) :
    ‖w‖^(2*N) < (2*(1-a/(2*(N : ℝ))))^8*((conj v*w).re)^(2*N-8) := by
  let m := 2*(N : ℝ)
  let x := (conj v*w).re
  let h := |(conj v*w).im|/x
  let R := 2*(1-a/m)
  have hx0 : 0 < x := hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hm : 0 < m := by dsimp [m]; positivity
  have hms : 0 < m-s := by dsimp [m]; linarith
  have hnorm : ‖conj v*w‖=‖w‖ := by rw [norm_mul, Complex.norm_conj, hv, one_mul]
  have hnorm2 : ‖w‖^2=x^2+(conj v*w).im^2 := by
    rw [←hnorm, Complex.sq_norm]
    simp only [Complex.normSq_apply, x, pow_two]
  have hfactor2 : ‖w‖^2=x^2*(1+h^2) := by
    rw [hnorm2]
    dsimp [h]
    rw [div_pow, sq_abs]
    field_simp [hx0.ne']
    <;> ring
  have hfactor : ‖w‖^(2*N)=x^(2*N)*(1+h^2)^N := by
    rw [pow_mul, hfactor2, mul_pow, ←pow_mul]
  have hratio : (m-a)/(m-s)=R/x := by
    have hxeq : x=2*(m-s)/m := by
      dsimp [x, m]
      rw [hxs]
      field_simp [hN0.ne']
      <;> ring
    have hReq : R=2*(m-a)/m := by
      dsimp [R]
      field_simp [hm.ne']
      <;> ring
    rw [hxeq, hReq]
    field_simp [hm.ne', hms.ne']
    <;> ring
  have hpower := far_power_ratio_of_angular_budget N (by omega : 1 ≤ N) ha has hs hcost
  change (1+h^2)^N < ((m-a)/(m-s))^8 at hpower
  rw [hratio] at hpower
  have hxp : x^(2*N)=x^(2*N-8)*x^8 := by
    rw [←pow_add]
    congr 1
    omega
  calc
    ‖w‖^(2*N)=x^(2*N)*(1+h^2)^N := hfactor
    _ < x^(2*N)*(R/x)^8 := mul_lt_mul_of_pos_left hpower (pow_pos hx (2*N))
    _ = R^8*x^(2*N-8) := by
      rw [div_pow, hxp]
      field_simp [hx0.ne']
      <;> ring

end SpringerLean

#print axioms SpringerLean.far_complex_power_le_lower_test
