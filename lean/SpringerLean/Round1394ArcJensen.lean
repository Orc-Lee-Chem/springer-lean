import SpringerLean.Round1393StrongArcConvex
import Mathlib.Analysis.Convex.Integral

open MeasureTheory

namespace SpringerLean

theorem coarseSmoothPower_arc_quantitative_Jensen
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let μ : ℝ := 2*Real.sin b/b
    let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
    (m/2)*((1/b)*(∫ θ in (0:ℝ)..b, (2*Real.cos θ)^2)-μ^2) ≤
      (1/b)*(∫ θ in (0:ℝ)..b,
        coarseSmoothRadius (2*Real.cos θ)^n) -
        coarseSmoothRadius μ^n := by
  dsimp
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let x₀ : ℝ := 2*Real.cos b
  let μ : ℝ := 2*Real.sin b/b
  let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
  let X : ℝ → ℝ := fun θ => 2*Real.cos θ
  let G : ℝ → ℝ := fun x => coarseSmoothRadius x^n-(m/2)*x^2
  let D : Set ℝ := Set.Icc x₀ 2
  have hb : 0 < b := (coarseArc_mean_bounds n hn).1
  have hbhalf : b ≤ Real.pi/2 := by
    have hsmall := coarseArc_b_le_one_twentieth n hn
    linarith [Real.pi_gt_three]
  have hμ := (coarseArc_mean_bounds n hn).2
  have hμD : μ ∈ D := ⟨hμ.1.le,hμ.2.2⟩
  have hconv : ConvexOn ℝ D G := by
    simpa [D,G,x₀,m,b] using coarseSmoothPower_sub_quadratic_convexOn n hn
  have hGcont : Continuous G := by
    dsimp [G,coarseSmoothRadius]
    fun_prop
  have hXcont : Continuous X := by dsimp [X]; fun_prop
  have hGXcont : Continuous (fun θ => G (X θ)) := hGcont.comp hXcont
  have hmeasure : volume.real (Set.Ioc (0:ℝ) b) = b := by
    simp [Measure.real, Real.volume_Ioc, hb.le]
  have hmeasure0 : volume (Set.Ioc (0:ℝ) b) ≠ 0 := by
    intro hzero
    have hz : volume.real (Set.Ioc (0:ℝ) b) = 0 := by
      simp [Measure.real, hzero]
    linarith
  have hmeasureTop : volume (Set.Ioc (0:ℝ) b) ≠ (⊤ : ENNReal) := by
    rw [Real.volume_Ioc]
    simp
  have hXrange : ∀ᵐ θ ∂volume.restrict (Set.Ioc (0:ℝ) b), X θ ∈ D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hθ.1.le
      (by linarith [hbhalf, Real.pi_pos]) hθ.2
    dsimp [D,X,x₀]
    constructor
    · linarith
    · linarith [Real.cos_le_one θ]
  have hXint : IntegrableOn X (Set.Ioc (0:ℝ) b) volume := by
    have hint : IntervalIntegrable X volume 0 b := hXcont.intervalIntegrable _ _
    exact hint.1
  have hGXint : IntegrableOn (fun θ => G (X θ)) (Set.Ioc (0:ℝ) b) volume := by
    have hint : IntervalIntegrable (fun θ => G (X θ)) volume 0 b :=
      hGXcont.intervalIntegrable _ _
    exact hint.1
  have hXmean : (1/b)*(∫ θ in (0:ℝ)..b, X θ) = μ := by
    dsimp [X,μ]
    rw [intervalIntegral.integral_const_mul]
    simp only [integral_cos, Real.sin_zero, sub_zero]
    have hbne : b ≠ 0 := ne_of_gt hb
    field_simp [hbne]
  have hAvgX : (⨍ θ in Set.Ioc (0:ℝ) b, X θ ∂volume) = μ := by
    rw [setAverage_eq, hmeasure]
    simp only [smul_eq_mul, inv_eq_one_div]
    rw [← intervalIntegral.integral_of_le hb.le]
    exact hXmean
  have hJ := hconv.map_set_average_le hGcont.continuousOn isClosed_Icc
    hmeasure0 hmeasureTop hXrange hXint hGXint
  rw [hAvgX, setAverage_eq, hmeasure] at hJ
  simp only [smul_eq_mul, inv_eq_one_div] at hJ
  rw [← intervalIntegral.integral_of_le hb.le] at hJ
  have hIntG : IntervalIntegrable (fun θ => coarseSmoothRadius (X θ)^n)
      volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [X,coarseSmoothRadius]
    fun_prop
  have hIntQ : IntervalIntegrable (fun θ => (m/2)*(X θ)^2)
      volume 0 b := by
    apply Continuous.intervalIntegrable
    dsimp [X]; fun_prop
  have hsplit : (∫ θ in (0:ℝ)..b, G (X θ)) =
      (∫ θ in (0:ℝ)..b, coarseSmoothRadius (X θ)^n) -
        (m/2)*(∫ θ in (0:ℝ)..b, (X θ)^2) := by
    dsimp [G]
    rw [intervalIntegral.integral_sub hIntG hIntQ]
    rw [intervalIntegral.integral_const_mul]
  rw [hsplit] at hJ
  dsimp [G] at hJ
  dsimp [X,μ,m,b] at *
  nlinarith

end SpringerLean

#print axioms SpringerLean.coarseSmoothPower_arc_quantitative_Jensen
