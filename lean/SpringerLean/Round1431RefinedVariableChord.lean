import SpringerLean.Round1430ActualAffineModelCost
import SpringerLean.Round1365ConvexChordExtension
import SpringerLean.Round1364ConvexChordScalar
import SpringerLean.Round1380EvenCircleIntegral

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 200000

/-- Keep the refined affine power up to the moving arc endpoint, then
continue by the secant through the arc mean. -/
noncomputable def refinedAffineChordPower
    (W : ℝ) (n : ℕ) (x₀ μ x : ℝ) : ℝ :=
  if x ≤ x₀ then refinedAffineRadius W x^n else
    refinedAffineRadius W x₀^n +
      (x-x₀)/(μ-x₀)*
        (refinedAffineRadius W μ^n-refinedAffineRadius W x₀^n)

theorem refinedAffineChordPower_convexOn
    (W : ℝ) (n : ℕ) {x₀ μ : ℝ} (hμ : x₀ < μ) :
    ConvexOn ℝ Set.univ (refinedAffineChordPower W n x₀ μ) := by
  change ConvexOn ℝ Set.univ (fun x =>
    if x ≤ x₀ then refinedAffineRadius W x^n else
      refinedAffineRadius W x₀^n +
        (x-x₀)/(μ-x₀)*
          (refinedAffineRadius W μ^n-refinedAffineRadius W x₀^n))
  exact convexProfile_right_chord_extension
    (fun x => refinedAffineRadius W x^n)
    (refinedAffineRadius_pow_convexOn W n) hμ

theorem refinedAffinePower_le_chordPower
    (W : ℝ) (n : ℕ) {x₀ μ x : ℝ}
    (hμ : x₀ < μ) (hx : x ≤ μ) :
    refinedAffineRadius W x^n ≤
      refinedAffineChordPower W n x₀ μ x := by
  by_cases hx₀ : x ≤ x₀
  · simp [refinedAffineChordPower,hx₀]
  · have hx₀' : x₀ ≤ x := le_of_lt (lt_of_not_ge hx₀)
    simp only [refinedAffineChordPower,if_neg hx₀]
    exact convexProfile_le_chord _
      (refinedAffineRadius_pow_convexOn W n) hμ hx₀' hx

/-- Exact moving-arc identity. The affine chord may cross the original
profile pointwise, but its average is the profile at the arc mean. -/
theorem refinedAffineChord_exact_arc_identity
    (W : ℝ) (n : ℕ) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ Real.pi/2)
    (hμ : 2*Real.cos b < 2*Real.sin b/b) :
    let x₀ : ℝ := 2*Real.cos b
    let μ : ℝ := 2*Real.sin b/b
    let V : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1
    let T : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W n x₀ μ (2*ζ.re)) 0 1
    V-T = (1/Real.pi)*
      ((∫ θ in (0:ℝ)..b,
        refinedAffineRadius W (2*Real.cos θ)^n) -
        b*refinedAffineRadius W μ^n) := by
  dsimp
  let x₀ : ℝ := 2*Real.cos b
  let μ : ℝ := 2*Real.sin b/b
  let f : ℝ → ℝ := fun x => refinedAffineRadius W x^n
  let t : ℝ → ℝ := refinedAffineChordPower W n x₀ μ
  have hbπ : b ≤ Real.pi := by linarith [Real.pi_pos]
  have hμ' : x₀ < μ := hμ
  have hfcont : Continuous f := by
    dsimp [f]
    have hr : Continuous (refinedAffineRadius W) := by
      unfold refinedAffineRadius
      fun_prop
    exact hr.pow n
  have htcont : Continuous t := by
    have hc := (refinedAffineChordPower_convexOn W n hμ').continuousOn
      isOpen_univ
    change Continuous (refinedAffineChordPower W n x₀ μ)
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
    have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
      hb0.le hθ'.2 hθ'.1
    have hx : 2*Real.cos θ ≤ x₀ := by dsimp [x₀]; linarith
    dsimp [g,j,t]
    simp [refinedAffineChordPower,hx,f]
  have hmean : b*μ=2*Real.sin b := by
    dsimp [μ]
    field_simp [ne_of_gt hb0]
  let c : ℝ := (f μ-f x₀)/(μ-x₀)
  have hline (x : ℝ) (hx : x₀ ≤ x) :
      t x = f μ+c*(x-μ) := by
    have hformula : f x₀+(x-x₀)/(μ-x₀)*(f μ-f x₀) =
        f μ+c*(x-μ) := by
      dsimp [c]
      field_simp [ne_of_gt (sub_pos.mpr hμ')]
      ring
    dsimp [t,refinedAffineChordPower]
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
        simpa [Set.uIcc_of_le hb0.le] using hθ
      have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
        hθ'.1 hbπ hθ'.2
      have hx : x₀ ≤ 2*Real.cos θ := by dsimp [x₀]; linarith
      exact hline _ hx
    rw [hcongr]
    have hInt : IntervalIntegrable
        (fun θ : ℝ => c*(2*Real.cos θ-μ)) volume 0 b := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_add intervalIntegrable_const hInt]
    rw [intervalIntegral.integral_const_mul]
    have hcosint : (∫ θ in (0:ℝ)..b,
        2*Real.cos θ-μ) = 0 := by
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const_mul]
        simp [integral_cos]
        linarith [hmean]
      · exact (by fun_prop : Continuous
          (fun θ : ℝ => 2*Real.cos θ)).intervalIntegrable _ _
      · exact intervalIntegrable_const
    rw [hcosint]
    simp
  rw [hV,hT]
  change (1/Real.pi)*(∫ θ in (0:ℝ)..Real.pi, g θ) -
    (1/Real.pi)*(∫ θ in (0:ℝ)..Real.pi, j θ) = _
  rw [hsplitg,hsplitj,houter,hinner]
  dsimp [g,f]
  ring

end SpringerLean

#print axioms SpringerLean.refinedAffineChordPower_convexOn
#print axioms SpringerLean.refinedAffineChord_exact_arc_identity
