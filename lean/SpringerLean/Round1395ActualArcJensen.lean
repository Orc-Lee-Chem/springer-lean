import SpringerLean.Round1394ArcJensen

open MeasureTheory

namespace SpringerLean

/-- Quantitative Jensen for the actual convex cap, after identifying
its smooth branch throughout the short comparison arc. -/
theorem coarseInversePower_arc_quantitative_Jensen
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let μ : ℝ := 2*Real.sin b/b
    let m : ℝ := (2:ℝ)^(n-2)*(n:ℝ)*(((n-1:ℕ):ℝ))/5
    (m/2)*((1/b)*(∫ θ in (0:ℝ)..b, (2*Real.cos θ)^2)-μ^2) ≤
      (1/b)*(∫ θ in (0:ℝ)..b,
        coarseInverseRadius (2*Real.cos θ)^n) -
        coarseInverseRadius μ^n := by
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let x₀ : ℝ := 2*Real.cos b
  let μ : ℝ := 2*Real.sin b/b
  have hb : 0 < b := (coarseArc_mean_bounds n hn).1
  have hbπ : b ≤ Real.pi := by
    have hsmall := coarseArc_b_le_one_twentieth n hn
    linarith [Real.pi_gt_three]
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hb2 : b^2=3/(n:ℝ) := Real.sq_sqrt (div_nonneg (by norm_num) hn0.le)
  have hbase : (31/16 : ℝ) ≤ x₀ := by
    have hdef := (coarseArc_cos_deficit_quadratic n hn hb.le (le_refl b)).2
    have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
    have hfrac : 3/(n:ℝ) ≤ 1/16 :=
      (div_le_iff₀ hn0).2 (by nlinarith)
    dsimp [x₀]
    linarith
  have hmean := (coarseArc_mean_bounds n hn).2
  have hμlo : (31/16 : ℝ) ≤ μ := hbase.trans hmean.1.le
  have hμhi : μ ≤ 2 := hmean.2.2
  have hμeq : coarseInverseRadius μ = coarseSmoothRadius μ :=
    coarseSmoothRadius_eq_active hμlo hμhi
  have hint :
      (∫ θ in (0:ℝ)..b, coarseInverseRadius (2*Real.cos θ)^n) =
      (∫ θ in (0:ℝ)..b, coarseSmoothRadius (2*Real.cos θ)^n) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.Icc 0 b := by
      simpa [Set.uIcc_of_le hb.le] using hθ
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hθ'.1 hbπ hθ'.2
    have hxlo : (31/16 : ℝ) ≤ 2*Real.cos θ := by
      dsimp [x₀] at hbase
      linarith
    have hxhi : 2*Real.cos θ ≤ 2 := by linarith [Real.cos_le_one θ]
    dsimp
    rw [coarseSmoothRadius_eq_active hxlo hxhi]
  have hJ := coarseSmoothPower_arc_quantitative_Jensen n hn
  dsimp at hJ ⊢
  rw [hint,hμeq]
  exact hJ

end SpringerLean

#print axioms SpringerLean.coarseInversePower_arc_quantitative_Jensen
