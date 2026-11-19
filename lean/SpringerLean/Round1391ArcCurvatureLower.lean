import SpringerLean.Round1390ArcCurvature

namespace SpringerLean

/-- Uniform curvature of the active power on the fixed short arc.
The constants use the strict `2/9` power factor and `9/10` slope
factor, whose product is `1/5`. -/
theorem coarseSmoothPower_arc_curvature_lower
    (n : ℕ) (hn : 1501 ≤ n) {x : ℝ}
    (hxlo : 2*Real.cos (Real.sqrt (3/(n:ℝ))) ≤ x)
    (hxhi : x ≤ 2) :
    (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5 ≤
      deriv (deriv (fun y : ℝ => coarseSmoothRadius y^n)) x := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hbase0 : 0 < 2-3/(n:ℝ) := by
    have hfrac : 3/(n:ℝ) < 1 := (div_lt_iff₀ hn0).2 (by linarith)
    linarith
  have hbase := coarseSmoothRadius_arc_lower n hn hxlo hxhi
  have hpow : (2/9 : ℝ)*(2:ℝ)^(n-2) <
      coarseSmoothRadius x^(n-2) := by
    have hfactor := coarseArc_power_factor_lower n hn
    have hfacpos : 0 < (2:ℝ)^(n-2) := by positivity
    have hbaseEq : 2-3/(n:ℝ) = 2*(1-3/(2*(n:ℝ))) := by ring
    calc
      (2/9 : ℝ)*(2:ℝ)^(n-2) =
          (2:ℝ)^(n-2)*(2/9 : ℝ) := by ring
      _ < (2:ℝ)^(n-2)*(1-3/(2*(n:ℝ)))^(n-2) :=
        mul_lt_mul_of_pos_left hfactor hfacpos
      _ = (2-3/(n:ℝ))^(n-2) := by rw [hbaseEq, mul_pow]
      _ ≤ coarseSmoothRadius x^(n-2) :=
        pow_le_pow_left₀ hbase0.le hbase (n-2)
  have hder := coarseSmoothRadius_arc_deriv_sq_lower n hn hxlo hxhi
  have hpow0 : 0 ≤ coarseSmoothRadius x^(n-2) := by
    exact pow_nonneg (hbase0.le.trans hbase) _
  have hprod : (1/5 : ℝ)*(2:ℝ)^(n-2) ≤
      coarseSmoothRadius x^(n-2)*(deriv coarseSmoothRadius x)^2 := by
    calc
      (1/5 : ℝ)*(2:ℝ)^(n-2) =
          ((2/9 : ℝ)*(2:ℝ)^(n-2))*(9/10 : ℝ) := by ring
      _ ≤ coarseSmoothRadius x^(n-2)*(9/10 : ℝ) :=
        mul_le_mul_of_nonneg_right hpow.le (by norm_num)
      _ ≤ coarseSmoothRadius x^(n-2)*(deriv coarseSmoothRadius x)^2 :=
        mul_le_mul_of_nonneg_left hder hpow0
  have hxA : x < 41/20 := by linarith
  have hsecond : 0 ≤ coarseSmoothRadius x^(n-1)*
      deriv (deriv coarseSmoothRadius) x :=
    mul_nonneg (pow_nonneg (hbase0.le.trans hbase) _)
      (coarseSmoothRadius_second_deriv_nonneg hxA)
  have hcoef : 0 ≤ (n:ℝ)*(((n-1:ℕ):ℝ)) := by positivity
  have hmult := mul_le_mul_of_nonneg_left hprod hcoef
  have hformula := coarseSmoothPower_second_deriv_formula n (by omega) hxA
  rw [hformula]
  nlinarith [hsecond,hmult]

end SpringerLean

#print axioms SpringerLean.coarseSmoothPower_arc_curvature_lower
