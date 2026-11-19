import SpringerLean.Round643ConvexUniformHinge
import SpringerLean.Round18FiniteConvex

namespace SpringerLean
set_option Elab.async false

/-- All positive-part tests and equal means imply every finite real convex
test on a common compact range. The approximation is proved above. -/
theorem circleAverage_convex_le_of_positivePart
    (X Y : ℂ → ℝ)
    (hX : ContinuousOn X (Metric.sphere (0 : ℂ) 1))
    (hY : ContinuousOn Y (Metric.sphere (0 : ℂ) 1))
    {a b : ℝ} (hab : a < b)
    (hXrange : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, X ζ ∈ Set.Icc a b)
    (hYrange : ∀ ζ ∈ Metric.sphere (0 : ℂ) 1, Y ζ ∈ Set.Icc a b)
    (hmean : Real.circleAverage X 0 1 = Real.circleAverage Y 0 1)
    (hhinge : ∀ c : ℝ,
      Real.circleAverage (fun ζ => max (X ζ-c) 0) 0 1 ≤
        Real.circleAverage (fun ζ => max (Y ζ-c) 0) 0 1)
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) :
    Real.circleAverage (fun ζ => ψ (X ζ)) 0 1 ≤
      Real.circleAverage (fun ζ => ψ (Y ζ)) 0 1 := by
  have hψc : Continuous ψ := by
    simpa only [continuousOn_univ] using (ConvexOn.continuousOn isOpen_univ hψ)
  have hψXi : CircleIntegrable (fun ζ => ψ (X ζ)) 0 1 :=
    (hψc.comp_continuousOn hX).circleIntegrable (by norm_num)
  have hψYi : CircleIntegrable (fun ζ => ψ (Y ζ)) 0 1 :=
    (hψc.comp_continuousOn hY).circleIntegrable (by norm_num)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨h,N,hh,htop,hw,happrox⟩ := convex_exists_grid_hinge_uniform ψ hψ hab hε
  let v : ℕ → ℝ := fun j => ψ (convexGridKnot a h j)
  let q : ℝ := convexGridSlope v h 0
  let t : ℕ → ℝ := fun j => convexGridKnot a h (j+1)
  let w : ℕ → ℝ := convexGridWeight v h
  let K : ℝ → ℝ := convexGridHinge v a h N
  have hKc : Continuous K := by
    change Continuous (fun x : ℝ => convexGridHinge v a h N x)
    dsimp only [convexGridHinge]
    fun_prop
  have hKXi : CircleIntegrable (fun ζ => K (X ζ)) 0 1 :=
    (hKc.comp_continuousOn hX).circleIntegrable (by norm_num)
  have hKYi : CircleIntegrable (fun ζ => K (Y ζ)) 0 1 :=
    (hKc.comp_continuousOn hY).circleIntegrable (by norm_num)
  have hshape (x : ℝ) : finiteHingeTest (Finset.range N) w t (v 0-q*a) q x = K x := by
    dsimp only [finiteHingeTest,K,convexGridHinge,w,t,q]
    ring
  have hPL := circleAverage_finiteHingeTest_le (Finset.range N) w t X Y hX hY hmean
    (fun i _ => hw i) (fun i _ => hhinge (t i)) (v 0-q*a) q
  simp_rw [hshape] at hPL
  have hlo : Real.circleAverage (fun ζ => ψ (X ζ)) 0 1 ≤
      Real.circleAverage (fun ζ => K (X ζ)) 0 1 := by
    apply Real.circleAverage_mono hψXi hKXi
    intro ζ hζ
    exact (happrox _ (hXrange ζ (by simpa only [abs_one] using hζ))).1
  have hψYεi : CircleIntegrable (fun ζ => ψ (Y ζ)+ε) 0 1 :=
    hψYi.add (circleIntegrable_const _ _ _)
  have hhi : Real.circleAverage (fun ζ => K (Y ζ)) 0 1 ≤
      Real.circleAverage (fun ζ => ψ (Y ζ)+ε) 0 1 := by
    apply Real.circleAverage_mono hKYi hψYεi
    intro ζ hζ
    exact (happrox _ (hYrange ζ (by simpa only [abs_one] using hζ))).2
  have hadd : Real.circleAverage (fun ζ => ψ (Y ζ)+ε) 0 1 =
      Real.circleAverage (fun ζ => ψ (Y ζ)) 0 1+ε := by
    rw [Real.circleAverage_fun_add hψYi (circleIntegrable_const _ _ _),
      Real.circleAverage_const]
  exact (hlo.trans hPL).trans (hhi.trans_eq hadd)

end SpringerLean
