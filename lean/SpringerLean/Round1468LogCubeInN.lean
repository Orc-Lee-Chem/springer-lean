import SpringerLean.Round1467LogCubeInT

namespace SpringerLean

/-- The normalized cubic logarithm decreases beyond the base order.
The same exponential envelope handles this without differentiating
`n/log(2n)^3`. -/
theorem logCube_n_envelope
    (n : ℕ) (hn : 1501 ≤ n) :
    (Real.log (2*(n:ℝ)))^3 ≤
      ((n:ℝ)/1501)*(Real.log 3002)^3 := by
  let N : ℝ := n
  let c : ℝ := Real.log 3002
  let u : ℝ := Real.log (N/1501)
  have hN : (1501:ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hratio : (1:ℝ) ≤ N/1501 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<1501)).2
    linarith
  have hratio0 : 0 < N/1501 := by positivity
  have hu : 0 ≤ u := Real.log_nonneg hratio
  have hc : 6 ≤ c := by dsimp [c]; linarith [log_3002_gt_six]
  have harg : 2*N=3002*(N/1501) := by ring
  have hL : Real.log (2*N)=c+u := by
    rw [harg,Real.log_mul (by norm_num : (3002:ℝ) ≠ 0)
      (ne_of_gt hratio0)]
  have hEnv := logCube_exponential_envelope hc hu
  have hExp : Real.exp (u/2) ≤ Real.exp u :=
    Real.exp_le_exp.mpr (by linarith)
  have hscaled := mul_le_mul_of_nonneg_left hExp
    (pow_nonneg (by linarith : 0 ≤ c) 3)
  have hle : (c+u)^3 ≤ c^3*(N/1501) := by
    calc
      (c+u)^3 ≤ c^3*Real.exp (u/2) := hEnv
      _ ≤ c^3*Real.exp u := hscaled
      _ = c^3*(N/1501) := by rw [show u=Real.log (N/1501) by rfl,
        Real.exp_log hratio0]
  rw [show (n:ℝ)=N by rfl,hL]
  dsimp [c]
  nlinarith [hle]

end SpringerLean

#print axioms SpringerLean.logCube_n_envelope
