import SpringerLean.Round1442CubicAverageGap
import Mathlib.Analysis.Convex.Integral

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 300000

/-- Quantitative Jensen on the moving arc. The cubic correction is
controlled by the raw cubic difference E[S³] − (E[S])³, leaving half of the variance. -/
theorem refinedAffineSmoothPower_moving_Jensen
    (n : ℕ) (hn : 1501 ≤ n)
    {W d : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hd0 : 0 < d) (hnd : (n:ℝ)*d < 1) :
    let b : ℝ := Real.sqrt (3*d)
    let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
    let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
    let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
    let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
      (2:ℝ)^(n-2)
    let B : ℝ := (n:ℝ)/2
    let s₀ : ℝ := 2*b^2/5
    (A*Real.exp (-B*s₀)/2)*var ≤
      (1/b)*(∫ θ in (0:ℝ)..b,
        refinedAffineSmoothPower W n (S θ)) -
        refinedAffineSmoothPower W n mean := by
  dsimp
  let b : ℝ := Real.sqrt (3*d)
  let S : ℝ → ℝ := fun θ => 2-2*Real.cos θ
  let mean : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ)
  let var : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^2)-mean^2
  let third : ℝ := (1/b)*(∫ θ in (0:ℝ)..b, S θ^3)-mean^3
  let A : ℝ := (refinedAffineV W)^2*(n:ℝ)*((n-1:ℕ):ℝ)*
    (2:ℝ)^(n-2)
  let B : ℝ := (n:ℝ)/2
  let s₀ : ℝ := 2*b^2/5
  let C : ℝ := A*Real.exp (-B*s₀)
  let f : ℝ → ℝ := refinedAffineSmoothPower W n
  let q : ℝ → ℝ := movingArcCubicQ B s₀
  let G : ℝ → ℝ := fun s => f s-C*q s
  let D : Set ℝ := Set.Icc 0 (b^2)
  have hnlarge : (1501:ℝ)≤n := by exact_mod_cast hn
  have hd : d ≤ 1/1501 := by
    have hh := mul_nonneg (sub_nonneg.mpr hnlarge) hd0.le
    nlinarith [hnd]
  have hb := (refinedArc_mean_bounds hd0 hd).1
  have hb0 : 0 ≤ b := hb.le
  have hbshort : b ≤ 1/20 := movingArc_b_le_one_twentieth hd0 hd
  have hconv : ConvexOn ℝ D G := by
    simpa [D,G,f,q,C,A,B,s₀,b] using
      (refinedAffineSmoothPower_cubic_corrected_convexOn
        n hn hW0 hW hd0 hnd)
  have hGcont : Continuous G := by
    dsimp [G,f,q,refinedAffineSmoothPower,movingArcCubicQ]
    fun_prop
  have hScont : Continuous S := by dsimp [S]; fun_prop
  have hGScont : Continuous (fun θ => G (S θ)) :=
    hGcont.comp hScont
  have hmeasure : volume.real (Set.Ioc (0:ℝ) b)=b := by
    simp [Measure.real,Real.volume_Ioc]
    exact hb0
  have hmeasure0 : volume (Set.Ioc (0:ℝ) b) ≠ 0 := by
    intro hz
    have hzero : volume.real (Set.Ioc (0:ℝ) b)=0 := by
      simp [Measure.real,hz]
    linarith
  have hmeasureTop : volume (Set.Ioc (0:ℝ) b) ≠ (⊤ : ENNReal) := by
    rw [Real.volume_Ioc]
    simp
  have hSrange : ∀ᵐ θ ∂volume.restrict (Set.Ioc (0:ℝ) b),
      S θ ∈ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hpoint := movingArc_cos_deficit_quadratic
      hbshort hθ.1.le hθ.2
    have hθsq : θ^2 ≤ b^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2)
        (add_nonneg hθ.1.le hb.le)]
    dsimp [D,S]
    constructor
    · linarith [Real.cos_le_one θ]
    · linarith [hpoint.2]
  have hSint : IntegrableOn S (Set.Ioc (0:ℝ) b) volume := by
    have hh : IntervalIntegrable S volume 0 b :=
      hScont.intervalIntegrable _ _
    exact hh.1
  have hGSint : IntegrableOn (fun θ => G (S θ))
      (Set.Ioc (0:ℝ) b) volume := by
    have hh : IntervalIntegrable (fun θ => G (S θ)) volume 0 b :=
      hGScont.intervalIntegrable _ _
    exact hh.1
  have hAvgS : (⨍ θ in Set.Ioc (0:ℝ) b,
      S θ ∂volume)=mean := by
    rw [setAverage_eq,hmeasure]
    simp only [smul_eq_mul,inv_eq_one_div]
    rw [← intervalIntegral.integral_of_le hb.le]
  have hJ := hconv.map_set_average_le hGcont.continuousOn isClosed_Icc
    hmeasure0 hmeasureTop hSrange hSint hGSint
  rw [hAvgS,setAverage_eq,hmeasure] at hJ
  simp only [smul_eq_mul,inv_eq_one_div] at hJ
  rw [← intervalIntegral.integral_of_le hb.le] at hJ
  have hIntF : IntervalIntegrable (fun θ => f (S θ)) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [f,S,refinedAffineSmoothPower]
    fun_prop
  have hIntQ : IntervalIntegrable (fun θ => C*q (S θ)) volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [q,S,movingArcCubicQ]
    fun_prop
  have hsplit : (∫ θ in (0:ℝ)..b, G (S θ)) =
      (∫ θ in (0:ℝ)..b, f (S θ)) -
        C*(∫ θ in (0:ℝ)..b, q (S θ)) := by
    dsimp [G]
    rw [intervalIntegral.integral_sub hIntF hIntQ]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit] at hJ
  have hQgap := movingArcCubicQ_average_gap hb B s₀
  change (1/b)*(∫ θ in (0:ℝ)..b, q (S θ))-q mean =
      (1+B*s₀)/2*var-B/6*third at hQgap
  have hthird := movingArc_third_moment_le_three_s0_variance hd0 hd
  change third ≤ 3*s₀*var at hthird
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hC0 : 0 ≤ C := by dsimp [C,A]; positivity
  have hthirdMul := mul_le_mul_of_nonneg_left hthird hB0
  have hQlower : var/2 ≤
      (1/b)*(∫ θ in (0:ℝ)..b, q (S θ))-q mean := by
    rw [hQgap]
    nlinarith [hthirdMul]
  have hClower := mul_le_mul_of_nonneg_left hQlower hC0
  change C/2*var ≤ (1/b)*(∫ θ in (0:ℝ)..b, f (S θ))-f mean
  dsimp [G] at hJ
  nlinarith [hJ,hClower]

end SpringerLean

#print axioms SpringerLean.refinedAffineSmoothPower_moving_Jensen
