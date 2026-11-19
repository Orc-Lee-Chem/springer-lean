import SpringerLean.Round1447MovingSavingScalar

open MeasureTheory

namespace SpringerLean

/-- The moving chord saves an explicit positive elementary expression.
This removes all integrals and variance symbols from the lower bound. -/
theorem refinedAffineChord_moving_saving_explicit
    (n : ℕ) (hn : 1501 ≤ n) {W d : ℝ}
    (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let b : ℝ := Real.sqrt (3*d)
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
      (2:ℝ)^(n-2)
    let B : ℝ := (n:ℝ)/2
    let s₀ : ℝ := 2*b^2/5
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W n x₀ μ (2*ζ.re)) 0 1
    (b/Real.pi)*(A*Real.exp (-B*s₀)/2)*
      ((995/1000:ℝ)*4*b^4/45) ≤ V-T := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*(2:ℝ)^(n-2)
  let B : ℝ := (n:ℝ)/2
  let s₀ : ℝ := 2*b^2/5
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
  let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hd : d ≤ 1/1501 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le]
  have hvar := movingArc_deficit_variance_lower hd0 hd
  change (995/1000:ℝ)*4*b^4/45 ≤ var at hvar
  have hsave := refinedAffineChord_moving_saving_variance
    n hn hW0 hW hd0 hnd
  change (b/Real.pi)*(A*Real.exp (-B*s₀)/2)*var ≤
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1 -
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W n
        (2*Real.cos b) (2*Real.sin b/b) (2*ζ.re)) 0 1 at hsave
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hcoef : 0 ≤ (b/Real.pi)*(A*Real.exp (-B*s₀)/2) := by
    dsimp [A]
    positivity
  have hmult := mul_le_mul_of_nonneg_left hvar hcoef
  nlinarith [hmult,hsave]

end SpringerLean

#print axioms SpringerLean.refinedAffineChord_moving_saving_explicit
