import SpringerLean.Round1361ExactInverseConvex

namespace SpringerLean
set_option maxHeartbeats 10000

/-- A convex profile lies below the line joining two values. This is
the pointwise part of the bad-end chord modification; its global
convexity and integrated Jensen gap are separate steps. -/
theorem convexProfile_le_chord
    (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f)
    {x₀ μ x : ℝ} (h₀μ : x₀ < μ)
    (h₀x : x₀ ≤ x) (hxμ : x ≤ μ) :
    f x ≤ f x₀ + (x-x₀)/(μ-x₀)*(f μ-f x₀) := by
  let a : ℝ := (μ-x)/(μ-x₀)
  let b : ℝ := (x-x₀)/(μ-x₀)
  have hden : 0 < μ-x₀ := by linarith
  have ha : 0 ≤ a := div_nonneg (by linarith) hden.le
  have hb : 0 ≤ b := div_nonneg (by linarith) hden.le
  have hab : a+b=1 := by
    dsimp [a,b]
    rw [← add_div, div_eq_one_iff_eq hden.ne']
    ring
  have hmix : a*x₀+b*μ=x := by
    dsimp [a,b]
    field_simp
    ring
  have hconv := hf.2 (Set.mem_univ x₀) (Set.mem_univ μ) ha hb hab
  simp only [smul_eq_mul] at hconv
  rw [hmix] at hconv
  have hline : a*f x₀+b*f μ = f x₀+b*(f μ-f x₀) := by
    calc
      a*f x₀+b*f μ = (a+b)*f x₀+b*(f μ-f x₀) := by ring
      _ = f x₀+b*(f μ-f x₀) := by rw [hab]; ring
  rw [hline] at hconv
  exact hconv

/-- The exact inverse profile's power can be paid by a chord on any
arc interval chosen for a bad selected endpoint. -/
theorem coarseInversePower_le_chord
    (n : ℕ) {x₀ μ x : ℝ} (h₀μ : x₀ < μ)
    (h₀x : x₀ ≤ x) (hxμ : x ≤ μ) :
    coarseInverseRadius x ^ n ≤
      coarseInverseRadius x₀ ^ n +
      (x-x₀)/(μ-x₀)*
        (coarseInverseRadius μ ^ n-coarseInverseRadius x₀ ^ n) := by
  exact convexProfile_le_chord _ (coarseInverseRadius_pow_convexOn n)
    h₀μ h₀x hxμ

end SpringerLean

#print axioms SpringerLean.convexProfile_le_chord
#print axioms SpringerLean.coarseInversePower_le_chord
