import SpringerLean.Round1364ConvexChordScalar
import Mathlib.Analysis.Convex.Slope

namespace SpringerLean
set_option maxHeartbeats 150000

/-- Extending a convex function to the right by the secant through
`a<b` preserves convexity. The secant slope dominates every left
slope, including when the interpolation crosses `a`. -/
theorem convexProfile_right_chord_extension
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    {a b : ℝ} (hab : a < b) :
    ConvexOn ℝ Set.univ
      (fun x => if x ≤ a then f x else
        f a+(x-a)/(b-a)*(f b-f a)) := by
  let m : ℝ := (f b-f a)/(b-a)
  let L : ℝ → ℝ := fun x => f a+m*(x-a)
  let g : ℝ → ℝ := fun x => if x ≤ a then f x else L x
  have hden : 0 < b-a := by linarith
  have hsupport (x : ℝ) (hxa : x ≤ a) : f a-f x ≤ m*(a-x) := by
    by_cases hxeq : x=a
    · subst x
      simp
    · have hxa' : x<a := lt_of_le_of_ne hxa hxeq
      have hsec := hf.slope_mono_adjacent
        (Set.mem_univ x) (Set.mem_univ b) hxa' hab
      change (f a-f x)/(a-x) ≤ m at hsec
      have h := (div_le_iff₀ (by linarith : 0<a-x)).1 hsec
      nlinarith
  have hgleft (x : ℝ) (hxa : x ≤ a) : g x = f x := by
    simp [g, hxa]
  have hgright (x : ℝ) (hax : a ≤ x) : g x = L x := by
    by_cases hxa : x ≤ a
    · have hxeq : x=a := le_antisymm hxa hax
      subst x
      simp [g,L]
    · simp [g,hxa]
  have hline (x y : ℝ) (hxy : x<y) :
      (L y-L x)/(y-x)=m := by
    dsimp [L]
    have hne : y-x ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have hgconv : ConvexOn ℝ Set.univ g := by
    apply convexOn_of_slope_mono_adjacent convex_univ
    intro x y z _ _ hxy hyz
    by_cases hza : z ≤ a
    · have hya : y ≤ a := le_trans hyz.le hza
      have hxa : x ≤ a := le_trans hxy.le hya
      rw [hgleft x hxa, hgleft y hya, hgleft z hza]
      exact hf.slope_mono_adjacent
        (Set.mem_univ x) (Set.mem_univ z) hxy hyz
    by_cases hax : a ≤ x
    · have hay : a ≤ y := hax.trans hxy.le
      have haz : a ≤ z := hay.trans hyz.le
      rw [hgright x hax, hgright y hay, hgright z haz,
        hline x y hxy, hline y z hyz]
    · have hxa : x < a := lt_of_not_ge hax
      have haz : a < z := lt_of_not_ge hza
      by_cases hay : a ≤ y
      · have hgy := hgright y hay
        have hgz := hgright z haz.le
        have hgx := hgleft x hxa.le
        rw [hgx,hgy,hgz,hline y z hyz]
        apply (div_le_iff₀ (by linarith : 0<y-x)).2
        dsimp [L]
        nlinarith [hsupport x hxa.le]
      · have hya : y<a := lt_of_not_ge hay
        have hgx := hgleft x hxa.le
        have hgy := hgleft y hya.le
        have hgz := hgright z haz.le
        rw [hgx,hgy,hgz]
        let p : ℝ := (f y-f x)/(y-x)
        have hp1 : p ≤ (f a-f y)/(a-y) := by
          exact hf.slope_mono_adjacent
            (Set.mem_univ x) (Set.mem_univ a) hxy hya
        have hp2 : (f a-f y)/(a-y) ≤ m := by
          exact hf.slope_mono_adjacent
            (Set.mem_univ y) (Set.mem_univ b) hya hab
        have hp3 : p*(a-y) ≤ f a-f y := by
          have hne : a-y ≠ 0 := ne_of_gt (by linarith)
          calc
            p*(a-y) ≤ ((f a-f y)/(a-y))*(a-y) :=
              mul_le_mul_of_nonneg_right hp1 (by linarith)
            _ = f a-f y := by field_simp
        have hp4 : p*(z-a) ≤ m*(z-a) :=
          mul_le_mul_of_nonneg_right (hp1.trans hp2) (by linarith)
        apply (le_div_iff₀ (by linarith : 0<z-y)).2
        dsimp [L]
        change p*(z-y) ≤ f a+m*(z-a)-f y
        nlinarith [hp3,hp4]
  convert hgconv using 1
  funext x
  by_cases hxa : x ≤ a
  · simp [g, hxa]
  · simp [g,hxa,L,m]
    ring

end SpringerLean

#print axioms SpringerLean.convexProfile_right_chord_extension
