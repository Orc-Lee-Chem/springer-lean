import SpringerLean.Round1382ModelCost
import SpringerLean.Round1367ArcMeanScalar

open MeasureTheory

namespace SpringerLean

private theorem chord_arc_angle_bounds (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    0 < b ∧ b ≤ Real.pi/2 := by
  dsimp
  have hb := (coarseArc_mean_bounds n hn).1
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hnlarge : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (Real.sqrt (3/(n:ℝ)))^2=3/(n:ℝ) :=
    Real.sq_sqrt (div_nonneg (by norm_num) hn0.le)
  have hsmall : Real.sqrt (3/(n:ℝ)) ≤ 1 := by
    have hdiv : (3:ℝ)/(n:ℝ) ≤ 1 := (div_le_iff₀ hn0).2 (by linarith)
    nlinarith
  exact ⟨hb, by linarith [Real.pi_gt_three]⟩

/-- Exact normalized arc identity, before estimating the Jensen gap.
The affine chord may cross the original profile pointwise on the arc;
only its average is used. -/
theorem coarseInverseChord_exact_arc_identity
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => coarseInverseChordPower n x₀ μ (2*ζ.re)) 0 1
    V-T = (1/Real.pi)*
      ((∫ θ in (0:ℝ)..b, coarseInverseRadius (2*Real.cos θ)^n) -
        b*coarseInverseRadius μ^n) := by
  dsimp
  let b : ℝ := Real.sqrt (3/(n:ℝ))
  let x₀ : ℝ := 2*Real.cos b
  let μ : ℝ := 2*Real.sin b/b
  let f : ℝ → ℝ := fun x => coarseInverseRadius x^n
  let t : ℝ → ℝ := coarseInverseChordPower n x₀ μ
  have hb := chord_arc_angle_bounds n hn
  have hb0 : 0 ≤ b := hb.1.le
  have hbπ : b ≤ Real.pi := by linarith [hb.2, Real.pi_pos]
  have hμ : x₀ < μ := (coarseArc_mean_bounds n hn).2.1
  have hfcont : Continuous f := coarseInverseRadius_continuous.pow n
  have htcont : Continuous t := by
    have hc := (coarseInverseChordPower_convexOn n hμ).continuousOn isOpen_univ
    change Continuous (coarseInverseChordPower n x₀ μ)
    simpa using hc
  have hV := evenCos_circleAverage_eq_integral f hfcont
  have hT := evenCos_circleAverage_eq_integral t htcont
  let g : ℝ → ℝ := fun θ => f (2*Real.cos θ)
  let j : ℝ → ℝ := fun θ => t (2*Real.cos θ)
  have hgcont : Continuous g := by dsimp [g]; fun_prop (disch := exact hfcont)
  have hjcont : Continuous j := by dsimp [j]; fun_prop (disch := exact htcont)
  have hsplitg : (∫ θ in (0:ℝ)..Real.pi, g θ) =
      (∫ θ in (0:ℝ)..b, g θ) +
        (∫ θ in b..Real.pi, g θ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hgcont.intervalIntegrable _ _) (hgcont.intervalIntegrable _ _)).symm
  have hsplitj : (∫ θ in (0:ℝ)..Real.pi, j θ) =
      (∫ θ in (0:ℝ)..b, j θ) +
        (∫ θ in b..Real.pi, j θ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hjcont.intervalIntegrable _ _) (hjcont.intervalIntegrable _ _)).symm
  have houter : (∫ θ in b..Real.pi, g θ) =
      ∫ θ in b..Real.pi, j θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hθ' : θ ∈ Set.Icc b Real.pi := by
      simpa [Set.uIcc_of_le hbπ] using hθ
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hb0 hθ'.2 hθ'.1
    have hx : 2*Real.cos θ ≤ x₀ := by dsimp [x₀]; linarith
    dsimp [g,j,t]
    simp [coarseInverseChordPower, hx, f]
  have hmean : b*μ=2*Real.sin b := by
    dsimp [μ]
    have hbne : b ≠ 0 := ne_of_gt hb.1
    field_simp [hbne]
  let c : ℝ := (f μ-f x₀)/(μ-x₀)
  have hden : μ-x₀ ≠ 0 := sub_ne_zero.mpr (ne_of_gt hμ)
  have hline (x : ℝ) (hx : x₀ ≤ x) :
      t x = f μ+c*(x-μ) := by
    have hformula : f x₀+(x-x₀)/(μ-x₀)*(f μ-f x₀) =
        f μ+c*(x-μ) := by
      dsimp [c]
      field_simp
      ring
    dsimp [t,coarseInverseChordPower]
    by_cases hxle : x ≤ x₀
    · have hxeq : x=x₀ := le_antisymm hxle hx
      subst x
      simp only [if_pos (le_refl x₀)]
      rw [← hformula]
      simp [f]
    · simp only [if_neg hxle]
      exact hformula
  have hinner : (∫ θ in (0:ℝ)..b, j θ) = b*f μ := by
    have hcongr : (∫ θ in (0:ℝ)..b, j θ) =
        ∫ θ in (0:ℝ)..b,
          (f μ+c*(2*Real.cos θ-μ)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc 0 b := by
        simpa [Set.uIcc_of_le hb0] using hθ
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hθ'.1 hbπ hθ'.2
      have hx : x₀ ≤ 2*Real.cos θ := by dsimp [x₀]; linarith
      exact hline _ hx
    rw [hcongr]
    have hInt : IntervalIntegrable
        (fun θ : ℝ => c*(2*Real.cos θ-μ)) volume 0 b := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_add (intervalIntegrable_const) hInt]
    rw [intervalIntegral.integral_const_mul]
    have hcosint : (∫ θ in (0:ℝ)..b, 2*Real.cos θ-μ) = 0 := by
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const_mul]
        simp [integral_cos]
        linarith [hmean]
      · exact (by fun_prop : Continuous (fun θ : ℝ => 2*Real.cos θ)).intervalIntegrable _ _
      · exact intervalIntegrable_const
    rw [hcosint]
    simp
  rw [hV,hT]
  change (1/Real.pi)*(∫ θ in (0:ℝ)..Real.pi, g θ) -
      (1/Real.pi)*(∫ θ in (0:ℝ)..Real.pi, j θ) = _
  rw [hsplitg,hsplitj,houter,hinner]
  dsimp [g,f]
  ring

theorem coarseInverseChord_exact_arc_mean_identity
    (n : ℕ) (hn : 1501 ≤ n) :
    let b : ℝ := Real.sqrt (3/(n:ℝ))
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => coarseInverseRadius (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => coarseInverseChordPower n x₀ μ (2*ζ.re)) 0 1
    V-T = (b/Real.pi)*
      ((1/b)*(∫ θ in (0:ℝ)..b,
        coarseInverseRadius (2*Real.cos θ)^n) -
        coarseInverseRadius μ^n) := by
  have h := coarseInverseChord_exact_arc_identity n hn
  dsimp at h ⊢
  have hb : Real.sqrt (3/(n:ℝ)) ≠ 0 :=
    ne_of_gt (chord_arc_angle_bounds n hn).1
  rw [h]
  field_simp [hb]

end SpringerLean

#print axioms SpringerLean.coarseInverseChord_exact_arc_identity
#print axioms SpringerLean.coarseInverseChord_exact_arc_mean_identity
