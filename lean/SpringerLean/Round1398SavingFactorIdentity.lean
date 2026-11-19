import SpringerLean.Round1397SavingNumeric

namespace SpringerLean

theorem coarseArc_saving_factor_identity
    (n : ℕ) (hn : 2 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
    (b/Real.pi)*(m/2)*((99/100 : ℝ)*4*b^4/45) =
      ((2:ℝ)^n/Real.sqrt (n:ℝ))*
        (Real.sqrt 3/(50*Real.pi))*(99/100 : ℝ)*(1-1/(n:ℝ)) := by
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  change (b/Real.pi)*(((2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5)/2)*
      ((99/100 : ℝ)*4*b^4/45) =
      ((2:ℝ)^n/Real.sqrt (n:ℝ))*
        (Real.sqrt 3/(50*Real.pi))*(99/100 : ℝ)*(1-1/(n:ℝ))
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnne : (n:ℝ) ≠ 0 := hn0.ne'
  have hrootpos : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hrootne : Real.sqrt (n:ℝ) ≠ 0 := hrootpos.ne'
  have hπne : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hbroot : b=Real.sqrt 3/Real.sqrt (n:ℝ) := by
    dsimp [b]
    exact Real.sqrt_div (by norm_num) _
  have hb4 : b^4=9/(n:ℝ)^2 := by
    have hb2 : b^2=3/(n:ℝ) := by
      dsimp [b]
      exact Real.sq_sqrt (div_nonneg (by norm_num) hn0.le)
    calc
      b^4=(b^2)^2 := by ring
      _=(3/(n:ℝ))^2 := by rw [hb2]
      _=9/(n:ℝ)^2 := by ring
  have hroot2 : (Real.sqrt (n:ℝ))^2=(n:ℝ) := Real.sq_sqrt hn0.le
  have hroot3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hcast : (((n-1:ℕ):ℝ))=(n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤n)]
    norm_num
  have hpow : (2:ℝ)^n=4*(2:ℝ)^(n-2) := by
    conv_lhs => rw [show n=(n-2)+2 by omega, pow_add]
    norm_num
    ring
  rw [hb4,hbroot,hcast,hpow]
  field_simp [hnne,hrootne,hπne]
  nlinarith [hroot2,hroot3]

end SpringerLean

#print axioms SpringerLean.coarseArc_saving_factor_identity
