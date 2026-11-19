import SpringerLean.Round1466Log3002Upper

namespace SpringerLean
set_option maxHeartbeats 200000

/-- At fixed order, the apparently singular factor
`sqrt(t) log(2n/t)^3` is maximized at `t=1`. The proof uses the
exponential cubic envelope and no derivatives. -/
theorem logCube_t_envelope
    (n : ℕ) (hn : 1501 ≤ n) {t : ℝ}
    (ht0 : 0 < t) (ht : t ≤ 1) :
    Real.sqrt t*(Real.log (2*(n:ℝ)/t))^3 ≤
      (Real.log (2*(n:ℝ)))^3 := by
  let N : ℝ := n
  let c : ℝ := Real.log (2*N)
  let u : ℝ := -Real.log t
  have hN : (1501:ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hc : 6 ≤ c := by
    have harg : (3002:ℝ) ≤ 2*N := by linarith
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<3002) harg
    dsimp [c]
    linarith [log_3002_gt_six]
  have hu : 0 ≤ u := by
    have hh := Real.log_le_log ht0 ht
    dsimp [u]
    simpa using hh
  have hL : Real.log (2*N/t)=c+u := by
    rw [Real.log_div (by positivity : 2*N ≠ 0) (ne_of_gt ht0)]
    dsimp [c,u]
    ring
  have hEnv := logCube_exponential_envelope hc hu
  have hsqE : (Real.exp (-u/2))^2=t := by
    rw [←Real.exp_nat_mul]
    have hx : (2:ℝ)*(-u/2)=Real.log t := by dsimp [u]; ring
    norm_num only [Nat.cast_ofNat]
    rw [hx,Real.exp_log ht0]
  have hsqrt : Real.sqrt t=Real.exp (-u/2) := by
    have hsq := Real.sq_sqrt ht0.le
    nlinarith [Real.sqrt_nonneg t,Real.exp_pos (-u/2)]
  have hprod : Real.sqrt t*Real.exp (u/2)=1 := by
    rw [hsqrt,←Real.exp_add]
    have hzero : -u/2+u/2=0 := by ring
    rw [hzero,Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_left hEnv
    (Real.sqrt_nonneg t)
  change Real.sqrt t*(c+u)^3 ≤
    Real.sqrt t*(c^3*Real.exp (u/2)) at hmul
  calc
    Real.sqrt t*(Real.log (2*(n:ℝ)/t))^3 =
        Real.sqrt t*(c+u)^3 := by rw [show (n:ℝ)=N by rfl,hL]
    _ ≤ Real.sqrt t*(c^3*Real.exp (u/2)) := hmul
    _ = c^3 := by
      calc
        Real.sqrt t*(c^3*Real.exp (u/2)) =
            c^3*(Real.sqrt t*Real.exp (u/2)) := by ring
        _ = c^3 := by rw [hprod]; ring

end SpringerLean

#print axioms SpringerLean.logCube_t_envelope
