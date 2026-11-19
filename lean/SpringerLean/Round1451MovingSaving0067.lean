import SpringerLean.Round1450MovingSavingNormalization

namespace SpringerLean
set_option maxHeartbeats 250000

/-- The moving-chord model saving with the paper's 0.067 coefficient.
The power `t^(5/2)` is written as `t^2*sqrt t`, so the dimensionless
deficit and its normalization remain transparent to Lean. -/
theorem refinedAffineChord_moving_saving_0067
    (n : ℕ) (hn : 1501 ≤ n) {W d : ℝ}
    (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let t : ℝ := (n:ℝ)*d
    let b : ℝ := Real.sqrt (3*d)
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let I : ℝ := Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W n x₀ μ (2*ζ.re)) 0 1
    (67/1000:ℝ)*I*t^2*Real.sqrt t*
      Real.exp (-(61/100:ℝ)*t) < V-T := by
  dsimp
  let N : ℝ := n
  let t : ℝ := N*d
  let r : ℝ := Real.sqrt N
  let v : ℝ := refinedAffineV W
  let I : ℝ := Real.circleAverage
    (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  let V : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
  let b : ℝ := Real.sqrt (3*d)
  let T : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineChordPower W n
      (2*Real.cos b) (2*Real.sin b/b) (2*ζ.re)) 0 1
  let p : ℝ := (2:ℝ)^n/r
  let c : ℝ := (Real.sqrt 3/(10*Real.pi))*(995/1000:ℝ)
  let ratio : ℝ := 1-1/N
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (by omega : 0<n)
  have hNlarge : (1501:ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast hn
  have ht : 0 < t := mul_pos hN hd0
  have hr : 0 < r := Real.sqrt_pos.2 hN
  have hp : 0 < p := div_pos (pow_pos (by norm_num) _) hr
  have hc : 0 < c := by dsimp [c]; positivity
  have hratio : (1500/1501:ℝ) ≤ ratio := by
    dsimp [ratio]
    have hdiv : 1/N ≤ 1/1501 := by
      apply (div_le_iff₀ hN).2
      nlinarith [hNlarge]
    linarith
  have hratio0 : 0 ≤ ratio := by linarith
  have hv : (49893/50000:ℝ) ≤ v := by
    dsimp [v,refinedAffineV]
    nlinarith [hW]
  have hv0 : 0 ≤ v := by linarith
  have hv2 : (49893/50000:ℝ)^2 ≤ v^2 :=
    pow_le_pow_left₀ (by norm_num) hv 2
  have hcoef : (67/1000:ℝ)*(4/5) < c*ratio*v^2 := by
    have hconst := refinedAffine_moving_saving_constant
    have hprod : (1500/1501:ℝ)*(49893/50000:ℝ)^2 ≤
        ratio*v^2 := by
      have h1 := mul_le_mul_of_nonneg_right hratio
        (sq_nonneg (49893/50000:ℝ))
      have h2 := mul_le_mul_of_nonneg_left hv2
        (by norm_num : (0:ℝ) ≤ 1500/1501)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hprod hc.le
    have hconst' : (67/1000:ℝ)*(4/5) <
        c*(1500/1501)*(49893/50000:ℝ)^2 := by
      dsimp [c]
      have hh := mul_lt_mul_of_pos_right hconst
        (by norm_num : (0:ℝ)<4/5)
      convert hh using 1 <;> (field_simp [Real.pi_ne_zero]; ring)
    nlinarith [hmul,hconst']
  have hI : I < (4/5:ℝ)*p := by
    have hh := comparisonCircleMoment_four_fifths_upper n
      (by omega : 1≤n)
    convert hh using 1 <;> (dsimp [I,p,N,r]; ring)
  have hMain : (67/1000:ℝ)*I < c*ratio*v^2*p := by
    have hh := mul_lt_mul_of_pos_left hI
      (by norm_num : (0:ℝ)<67/1000)
    have hh2 := mul_lt_mul_of_pos_right hcoef hp
    nlinarith [hh,hh2]
  have hExp : Real.exp (-(61/100:ℝ)*t) ≤
      Real.exp (-(3/5:ℝ)*t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [ht]
  have hNonneg : 0 ≤ (67/1000:ℝ)*I := by
    have hI0 : 0 ≤ I := by
      dsimp [I]
      apply Real.circleAverage_nonneg_of_nonneg
      intro z hz
      exact pow_nonneg (abs_nonneg _) _
    positivity
  have hScale : 0 < t^2*Real.sqrt t := by positivity
  have hCompare :
      (67/1000:ℝ)*I*t^2*Real.sqrt t*
        Real.exp (-(61/100:ℝ)*t) <
      c*ratio*v^2*p*t^2*Real.sqrt t*
        Real.exp (-(3/5:ℝ)*t) := by
    have hmul := mul_lt_mul_of_pos_right hMain
      (mul_pos hScale (Real.exp_pos (-(3/5:ℝ)*t)))
    have hexpmul := mul_le_mul_of_nonneg_left hExp
      (mul_nonneg hNonneg hScale.le)
    nlinarith [hmul,hexpmul]
  have hnorm := movingArc_explicit_saving_normalization n hn
    (W := W) hd0
  have hexplicit := refinedAffineChord_moving_saving_explicit
    n hn hW0 hW hd0 hnd
  change (Real.sqrt (3*d)/Real.pi)*
      ((v^2*N*((n-1:ℕ):ℝ)*(2:ℝ)^(n-2))*
        Real.exp (-(N/2)*(2*b^2/5))/2)*
      ((995/1000:ℝ)*4*b^4/45) ≤ V-T at hexplicit
  change (Real.sqrt (3*d)/Real.pi)*
      ((v^2*N*((n-1:ℕ):ℝ)*(2:ℝ)^(n-2))*
        Real.exp (-(N/2)*(2*b^2/5))/2)*
      ((995/1000:ℝ)*4*b^4/45) =
      c*ratio*v^2*p*t^2*Real.sqrt t*
        Real.exp (-(3/5:ℝ)*t) at hnorm
  rw [hnorm] at hexplicit
  exact lt_of_lt_of_le hCompare hexplicit

end SpringerLean

#print axioms SpringerLean.refinedAffineChord_moving_saving_0067
