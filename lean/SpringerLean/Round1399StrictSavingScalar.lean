import SpringerLean.Round1398SavingFactorIdentity
import SpringerLean.Round1375OddCosUpper

namespace SpringerLean

theorem coarseArc_strict_saving_scalar
    (k : ℕ) (hk : 751 ≤ k) :
    let n : ℕ := 2*k-1
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
    let I : ℝ := Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1
    I/100 < (b/Real.pi)*(m/2)*((99/100 : ℝ)*4*b^4/45) := by
  dsimp
  let n : ℕ := 2*k-1
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
  let I : ℝ := Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hroot : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hupper : I ≤ (2:ℝ)^n/Real.sqrt (n:ℝ) := by
    have hidx : 2*(k-1)+1=n := by dsimp [n]; omega
    simpa [hidx,I] using comparisonCircleMoment_odd_le_two_pow_div_sqrt (k-1)
  have hratio := coarseArc_relative_saving_gt_centipercent n hn
  have hfactor := coarseArc_saving_factor_identity n (by omega)
  change (b/Real.pi)*(m/2)*((99/100 : ℝ)*4*b^4/45) = _ at hfactor
  have hpowpos : 0 < (2:ℝ)^n/Real.sqrt (n:ℝ) := by positivity
  have hfirst : I/100 ≤ ((2:ℝ)^n/Real.sqrt (n:ℝ))/100 :=
    div_le_div_of_nonneg_right hupper (by norm_num)
  have hsecond : ((2:ℝ)^n/Real.sqrt (n:ℝ))/100 <
      ((2:ℝ)^n/Real.sqrt (n:ℝ))*
        (Real.sqrt 3/(50*Real.pi))*(99/100 : ℝ)*(1-1/(n:ℝ)) := by
    have hh := mul_lt_mul_of_pos_left hratio hpowpos
    convert hh using 1 <;> ring
  change I/100 < (b/Real.pi)*(m/2)*((99/100 : ℝ)*4*b^4/45)
  exact hfirst.trans_lt (hsecond.trans_eq hfactor.symm)

end SpringerLean

#print axioms SpringerLean.coarseArc_strict_saving_scalar
