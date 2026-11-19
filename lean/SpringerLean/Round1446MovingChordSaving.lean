import SpringerLean.Round1445MovingChordCurvature

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 350000

/-- Quantitative saving for the exact moving chord. This theorem keeps
the variance and exponential curvature in the same unscaled circle
normalization as the model cost. -/
theorem refinedAffineChord_moving_saving_variance
    (n : ℕ) (hn : 1501 ≤ n) {W d : ℝ}
    (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let b : ℝ := Real.sqrt (3*d)
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
    let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
    let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
      (2:ℝ)^(n-2)
    let B : ℝ := (n:ℝ)/2
    let s₀ : ℝ := 2*b^2/5
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W n x₀ μ (2*ζ.re)) 0 1
    (b/Real.pi)*(A*Real.exp (-B*s₀)/2)*var ≤ V-T := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
  let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
  let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*(2:ℝ)^(n-2)
  let B : ℝ := (n:ℝ)/2
  let s₀ : ℝ := 2*b^2/5
  let x₀ : ℝ := 2*Real.cos b
  let μ : ℝ := 2*Real.sin b/b
  let V : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
  let T : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineChordPower W n x₀ μ (2*ζ.re)) 0 1
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hd : d ≤ 1/1501 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le]
  have hb : 0 < b := (refinedArc_mean_bounds hd0 hd).1
  have hJ := refinedAffineSmoothPower_moving_Jensen n hn hW0 hW hd0 hnd
  change (A*Real.exp (-B*s₀)/2)*var ≤
    (1/b)*(∫ θ in (0:ℝ)..b,
      refinedAffineSmoothPower W n (S θ)) -
      refinedAffineSmoothPower W n mean at hJ
  have hArcEq : (∫ θ in (0:ℝ)..b,
      refinedAffineRadius W (2*Real.cos θ)^n) =
      ∫ θ in (0:ℝ)..b,
        refinedAffineSmoothPower W n (S θ) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.Icc 0 b := by
      simpa [Set.uIcc_of_le hb.le] using hθ
    exact refinedAffine_moving_arc_profile_eq n hn hW0 hW hd0 hnd
      hθ'.1 hθ'.2
  have hMeanEq : refinedAffineRadius W μ^n =
      refinedAffineSmoothPower W n mean :=
    refinedAffine_moving_mean_profile_eq n hn hW0 hW hd0 hnd
  have hIdentity := refinedAffineChord_moving_arc_mean_identity
    W n hd0 hd
  change V-T=(b/Real.pi)*
    ((1/b)*(∫ θ in (0:ℝ)..b,
      refinedAffineRadius W (2*Real.cos θ)^n) -
      refinedAffineRadius W μ^n) at hIdentity
  rw [hArcEq,hMeanEq] at hIdentity
  rw [hIdentity]
  have hmul := mul_le_mul_of_nonneg_left hJ
    (div_nonneg hb.le Real.pi_pos.le)
  convert hmul using 1 <;> (dsimp [b,S,mean,var,A,B,s₀]; ring)

end SpringerLean

#print axioms SpringerLean.refinedAffineChord_moving_saving_variance
