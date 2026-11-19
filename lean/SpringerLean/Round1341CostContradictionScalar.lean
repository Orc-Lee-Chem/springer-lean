import SpringerLean.Round1337PlatformScalar

namespace SpringerLean

/-- Once the one-sided model cost and the platform estimate are known,
the candidate lower bound gives a strict contradiction at every `n ≥ 1501`. -/
theorem one_side_model_cost_lt_candidate
    (n : ℕ) (hn : 1501 ≤ n) {I U : ℝ} (hI : 0 < I)
    (hplatform : 2 * (39/20 : ℝ)^n ≤ I / n)
    (hcost : U ≤ (39/20 : ℝ)^n + (I/2) * (1 + 13/(n:ℝ))) :
    U < (1 - 1/(n:ℝ)) * I := by
  have hnR : (1501 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hnum := one_side_cost_contradiction_scalar n hn
  have hplat : (39/20 : ℝ)^n ≤ I/(2*n) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 2*n)).2
    have hp := (le_div_iff₀ hn0).mp hplatform
    nlinarith [hp]
  have hupper : U ≤ (1/2 + 7/(n:ℝ))*I := by
    calc
      U ≤ (39/20 : ℝ)^n + (I/2) * (1 + 13/(n:ℝ)) := hcost
      _ ≤ I/(2*n) + (I/2) * (1 + 13/(n:ℝ)) := by
        simpa only [add_comm] using
          (add_le_add_right hplat ((I/2) * (1 + 13/(n:ℝ))))
      _ = (1/2 + 7/(n:ℝ))*I := by field_simp; ring
  exact hupper.trans_lt (mul_lt_mul_of_pos_right hnum hI)

/-- A single bad-end chord saving of more than `I/100` pays both
unmodified model costs at `n ≥ 1501`. -/
theorem two_side_model_cost_lt_candidate
    (n : ℕ) (hn : 1501 ≤ n) {I U : ℝ} (hI : 0 < I)
    (hplatform : 2 * (39/20 : ℝ)^n ≤ I / n)
    (hcost : U + I/100 < 2 * (39/20 : ℝ)^n + I * (1 + 13/(n:ℝ))) :
    U < (1 - 1/(n:ℝ)) * I := by
  have hnR : (1501 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h15 : (15:ℝ)/(n:ℝ) < 1/100 := by
    apply (div_lt_iff₀ hn0).2
    linarith
  have hbudget : U + I/100 < I * (1 + 14/(n:ℝ)) := by
    have hp : 2 * (39/20 : ℝ)^n + I * (1 + 13/(n:ℝ)) ≤
        I / n + I * (1 + 13/(n:ℝ)) := by
      simpa only [add_comm] using
        (add_le_add_right hplatform (I * (1 + 13/(n:ℝ))))
    have heq : I / n + I * (1 + 13/(n:ℝ)) =
        I * (1 + 14/(n:ℝ)) := by field_simp; ring
    exact (hcost.trans_le hp).trans_eq heq
  have hstrict : I * (1 + 14/(n:ℝ)) - I/100 < (1 - 1/(n:ℝ))*I := by
    have hs := mul_lt_mul_of_pos_right h15 hI
    have hh : (15 / (n:ℝ))*I < I/100 := by nlinarith [hs]
    calc
      I * (1 + 14/(n:ℝ)) - I/100 <
          I * (1 + 14/(n:ℝ)) - (15 / (n:ℝ))*I :=
        sub_lt_sub_left hh _
      _ = (1 - 1/(n:ℝ))*I := by ring
  linarith

end SpringerLean

#print axioms SpringerLean.one_side_model_cost_lt_candidate
#print axioms SpringerLean.two_side_model_cost_lt_candidate
