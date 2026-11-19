import SpringerLean.Round642ConvexGridBounds
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.UniformSpace.HeineCantor

namespace SpringerLean
set_option Elab.async false

/-- Every finite real convex function has finite convex hinge interpolants
uniformly above it on a prescribed compact interval, with arbitrary error. -/
theorem convex_exists_grid_hinge_uniform
    (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ)
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) :
    ∃ (h : ℝ) (N : ℕ), 0 < h ∧ convexGridKnot a h (N+1)=b ∧
      (∀ i : ℕ, 0 ≤ convexGridWeight (fun j => ψ (convexGridKnot a h j)) h i) ∧
      ∀ x ∈ Set.Icc a b,
        ψ x ≤ convexGridHinge (fun j => ψ (convexGridKnot a h j)) a h N x ∧
        convexGridHinge (fun j => ψ (convexGridKnot a h j)) a h N x ≤ ψ x+ε := by
  have hcont : Continuous ψ := by
    simpa only [continuousOn_univ] using (ConvexOn.continuousOn isOpen_univ hψ)
  have huni := isCompact_Icc.uniformContinuousOn_of_continuous
    (s := Set.Icc a b) hcont.continuousOn
  obtain ⟨δ,hδ,hclose⟩ := (Metric.uniformContinuousOn_iff.mp huni) ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/δ)
  let h : ℝ := (b-a)/((N : ℝ)+1)
  have hNp : 0 < (N : ℝ)+1 := by positivity
  have hh : 0 < h := div_pos (sub_pos.mpr hab) hNp
  have hmesh : h < δ := by
    apply (div_lt_iff₀ hNp).mpr
    have hn := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have htop : convexGridKnot a h (N+1)=b := by
    dsimp only [convexGridKnot,h]
    push_cast
    field_simp [ne_of_gt hNp]
    <;> ring
  refine ⟨h,N,hh,htop,(fun i => convexGridWeight_nonneg_of_convex ψ hψ a hh i),?_⟩
  intro x hx
  obtain ⟨i,hi,hlo,hhi⟩ := convexGrid_cell_exists a h N x hx.1
    (by simpa only [htop] using hx.2)
  have hmono := convexGridKnot_mono a hh.le
  have hstep : convexGridKnot a h (i+1)=convexGridKnot a h i+h := by
    dsimp only [convexGridKnot]
    push_cast
    ring
  have hlow : convexGridKnot a h i ∈ Set.Icc a b := by
    constructor
    · dsimp only [convexGridKnot]
      linarith [mul_nonneg (Nat.cast_nonneg i) hh.le]
    · rw [← htop]
      exact hmono (by omega)
  have hhigh : convexGridKnot a h (i+1) ∈ Set.Icc a b := by
    constructor
    · dsimp only [convexGridKnot]
      linarith [mul_nonneg (Nat.cast_nonneg (i+1)) hh.le]
    · rw [← htop]
      exact hmono (Nat.add_le_add_right hi 1)
  have hdlo : dist (convexGridKnot a h i) x < δ := by
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  have hdhi : dist (convexGridKnot a h (i+1)) x < δ := by
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hhi)]
    linarith
  have hvlo : ψ (convexGridKnot a h i) ≤ ψ x+ε := by
    have hc := hclose _ hlow x hx hdlo
    rw [Real.dist_eq] at hc
    linarith [le_abs_self (ψ (convexGridKnot a h i)-ψ x)]
  have hvhi : ψ (convexGridKnot a h (i+1)) ≤ ψ x+ε := by
    have hc := hclose _ hhigh x hx hdhi
    rw [Real.dist_eq] at hc
    linarith [le_abs_self (ψ (convexGridKnot a h (i+1))-ψ x)]
  exact ⟨convexGridHinge_ge_of_convex ψ hψ a hh hi hlo hhi,
    convexGridHinge_le_of_cell_values _ a hh hi hlo hhi hvlo hvhi⟩

end SpringerLean
