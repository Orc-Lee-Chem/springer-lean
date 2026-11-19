import SpringerLean.Round1448MovingSavingExplicit

namespace SpringerLean

/-- Isolates the only square-root algebra in the moving-chord
normalization. `t=N*d` is the dimensionless deficit. -/
theorem movingArc_root_normalization
    {N d b r q : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hb2 : b^2=3*d) (hbr : b*r=Real.sqrt 3*q) :
    b^5*N*(N-1) =
      9*Real.sqrt 3*(1-1/N)*((N*d)^2*q/r) := by
  have hbfour : b^4=9*d^2 := by
    calc
      b^4=(b^2)^2 := by ring
      _=9*d^2 := by rw [hb2]; ring
  have hb5r : b^5*r=9*Real.sqrt 3*d^2*q := by
    calc
      b^5*r=b^4*(b*r) := by ring
      _=9*Real.sqrt 3*d^2*q := by rw [hbfour,hbr]; ring
  field_simp [ne_of_gt hN,ne_of_gt hr]
  nlinarith [hb5r]

theorem movingArc_sqrt_factor
    {n : ℕ} (hn : 1 ≤ n) {d : ℝ} (hd : 0 ≤ d) :
    Real.sqrt (3*d)*Real.sqrt (n:ℝ) =
      Real.sqrt 3*Real.sqrt ((n:ℝ)*d) := by
  rw [Real.sqrt_mul (by positivity : 0 ≤ (3:ℝ)) d]
  rw [Real.sqrt_mul (by positivity : 0 ≤ (n:ℝ)) d]
  ring

end SpringerLean

#print axioms SpringerLean.movingArc_root_normalization
#print axioms SpringerLean.movingArc_sqrt_factor
