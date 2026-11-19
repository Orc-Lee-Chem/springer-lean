import SpringerLean.Round1399StrictSavingScalar

open MeasureTheory

namespace SpringerLean

/-- The precise scalar saving premise in the actual two-end deficit
reduction. Both selected bad-end tests use this same model circle. -/
theorem coarseInverseChord_strict_circle_saving
    (k : ℕ) (hk : 751 ≤ k) :
    let n : ℕ := 2*k-1
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let I : ℝ := Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => coarseInverseChordPower n x₀ μ (2*ζ.re)) 0 1
    T+I/100<V := by
  let n : ℕ := 2*k-1
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let x₀ : ℝ := 2*Real.cos b
  let μ : ℝ := 2*Real.sin b/b
  let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
  let I : ℝ := Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  let V : ℝ := Real.circleAverage
    (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1
  let T : ℝ := Real.circleAverage
    (fun ζ : ℂ => coarseInverseChordPower n x₀ μ (2*ζ.re)) 0 1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hb : 0 < b := (coarseArc_mean_bounds n hn).1
  have hπ : 0 < Real.pi := Real.pi_pos
  have hm : 0 ≤ m/2 := by dsimp [m]; positivity
  have hvar := coarseArc_projection_variance_lower n hn
  change (99/100 : ℝ)*4*b^4/45 ≤
      (1/b)*(∫ θ in (0:ℝ)..b, (2*Real.cos θ)^2)-μ^2 at hvar
  have hJ := coarseInversePower_arc_quantitative_Jensen n hn
  change (m/2)*((1/b)*(∫ θ in (0:ℝ)..b,
      (2*Real.cos θ)^2)-μ^2) ≤
      (1/b)*(∫ θ in (0:ℝ)..b,
        coarseInverseRadius (2*Real.cos θ)^n)-
        coarseInverseRadius μ^n at hJ
  have hpaid : (m/2)*((99/100 : ℝ)*4*b^4/45) ≤
      (1/b)*(∫ θ in (0:ℝ)..b,
        coarseInverseRadius (2*Real.cos θ)^n)-
        coarseInverseRadius μ^n :=
    (mul_le_mul_of_nonneg_left hvar hm).trans hJ
  have hpaid' := mul_le_mul_of_nonneg_left hpaid
    (show 0 ≤ b/Real.pi by positivity)
  have hArc := coarseInverseChord_exact_arc_mean_identity n hn
  change V-T=(b/Real.pi)*
      ((1/b)*(∫ θ in (0:ℝ)..b,
        coarseInverseRadius (2*Real.cos θ)^n)-
        coarseInverseRadius μ^n) at hArc
  have hstrict := coarseArc_strict_saving_scalar k hk
  change I/100 < (b/Real.pi)*(m/2)*((99/100 : ℝ)*4*b^4/45) at hstrict
  change T+I/100<V
  nlinarith

end SpringerLean

#print axioms SpringerLean.coarseInverseChord_strict_circle_saving
