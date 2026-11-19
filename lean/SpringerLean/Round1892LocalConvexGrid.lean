import SpringerLean.Round643ConvexUniformHinge

namespace SpringerLean
set_option Elab.async false

/- The grid approximation below only samples the prescribed compact
   interval.  Convexity outside that interval is irrelevant. -/
private theorem knot_mem_Icc
    {a b h : ℝ} {N j : ℕ} (hh : 0 ≤ h)
    (htop : convexGridKnot a h (N + 1) = b) (hj : j ≤ N + 1) :
    convexGridKnot a h j ∈ Set.Icc a b := by
  constructor
  · dsimp [convexGridKnot]
    nlinarith [mul_nonneg (Nat.cast_nonneg j) hh]
  · rw [← htop]
    exact convexGridKnot_mono a hh hj

private theorem grid_weight_nonneg_local
    (f : ℝ → ℝ) {a b h : ℝ} {N i : ℕ}
    (hh : 0 < h) (htop : convexGridKnot a h (N + 1) = b)
    (hi : i < N) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    0 ≤ convexGridWeight (fun j => f (convexGridKnot a h j)) h i := by
  apply convexGridWeight_nonneg _ hh
  have hleft := knot_mem_Icc hh.le htop (show i ≤ N + 1 by omega)
  have hright := knot_mem_Icc hh.le htop (show i + 2 ≤ N + 1 by omega)
  have hmid := hf.2 hleft hright
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hp : (1 / 2 : ℝ) * convexGridKnot a h i +
      (1 / 2 : ℝ) * convexGridKnot a h (i + 2) =
      convexGridKnot a h (i + 1) := by
    dsimp [convexGridKnot]
    push_cast
    ring
  simp only [smul_eq_mul, hp] at hmid
  convert hmid using 1 <;> ring

private theorem grid_hinge_ge_local
    (f : ℝ → ℝ) {a b h : ℝ} {N i : ℕ} {x : ℝ}
    (hh : 0 < h) (htop : convexGridKnot a h (N + 1) = b)
    (hi : i ≤ N) (hlo : convexGridKnot a h i ≤ x)
    (hhi : x ≤ convexGridKnot a h (i + 1))
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    f x ≤ convexGridHinge (fun j => f (convexGridKnot a h j)) a h N x := by
  let t := (x - convexGridKnot a h i) / h
  have ht := convexGrid_cell_fraction_mem_unit a hh i hlo hhi
  have hpoint : (1 - t) * convexGridKnot a h i +
      t * convexGridKnot a h (i + 1) = x := by
    dsimp [t, convexGridKnot]
    push_cast
    field_simp [hh.ne']
    <;> ring
  have hleft := knot_mem_Icc hh.le htop (show i ≤ N + 1 by omega)
  have hright := knot_mem_Icc hh.le htop (show i + 1 ≤ N + 1 by omega)
  have hc := hf.2 hleft hright
    (show (0 : ℝ) ≤ 1 - t by linarith [ht.2])
    ht.1 (show 1 - t + t = 1 by ring)
  simp only [smul_eq_mul] at hc
  rw [hpoint] at hc
  rw [convexGridHinge_eq_chord _ a hh hi hlo hhi]
  exact hc

/-- A locally convex function has nonnegative finite-hinge grid weights and
an arbitrarily close interpolation on exactly the compact interval used by
the boundary projection. -/
theorem convex_exists_grid_hinge_uniform_local
    (f : ℝ → ℝ) {a b ε : ℝ} (hab : a < b) (hε : 0 < ε)
    (hf : ConvexOn ℝ (Set.Icc a b) f)
    (hcont : ContinuousOn f (Set.Icc a b)) :
    ∃ (h : ℝ) (N : ℕ), 0 < h ∧ convexGridKnot a h (N + 1) = b ∧
      (∀ i : ℕ, i < N →
        0 ≤ convexGridWeight (fun j => f (convexGridKnot a h j)) h i) ∧
      ∀ x ∈ Set.Icc a b,
        f x ≤ convexGridHinge (fun j => f (convexGridKnot a h j)) a h N x ∧
        convexGridHinge (fun j => f (convexGridKnot a h j)) a h N x ≤ f x + ε := by
  have huni := isCompact_Icc.uniformContinuousOn_of_continuous hcont
  obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuousOn_iff.mp huni) ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  let h : ℝ := (b - a) / ((N : ℝ) + 1)
  have hNp : 0 < (N : ℝ) + 1 := by positivity
  have hh : 0 < h := div_pos (sub_pos.mpr hab) hNp
  have hmesh : h < δ := by
    apply (div_lt_iff₀ hNp).mpr
    have hn := (div_lt_iff₀ hδ).mp hN
    nlinarith
  have htop : convexGridKnot a h (N + 1) = b := by
    dsimp [convexGridKnot, h]
    push_cast
    field_simp [ne_of_gt hNp]
    <;> ring
  refine ⟨h, N, hh, htop, (fun i hi =>
    grid_weight_nonneg_local f hh htop hi hf), ?_⟩
  intro x hx
  obtain ⟨i, hi, hlo, hhi⟩ := convexGrid_cell_exists a h N x hx.1
    (by simpa only [htop] using hx.2)
  have hmono := convexGridKnot_mono a hh.le
  have hstep : convexGridKnot a h (i + 1) = convexGridKnot a h i + h := by
    dsimp [convexGridKnot]
    push_cast
    ring
  have hlow := knot_mem_Icc hh.le htop (show i ≤ N + 1 by omega)
  have hhigh := knot_mem_Icc hh.le htop (show i + 1 ≤ N + 1 by omega)
  have hdlo : dist (convexGridKnot a h i) x < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  have hdhi : dist (convexGridKnot a h (i + 1)) x < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hhi)]
    linarith
  have hvlo : f (convexGridKnot a h i) ≤ f x + ε := by
    have hc := hclose _ hlow x hx hdlo
    rw [Real.dist_eq] at hc
    linarith [le_abs_self (f (convexGridKnot a h i) - f x)]
  have hvhi : f (convexGridKnot a h (i + 1)) ≤ f x + ε := by
    have hc := hclose _ hhigh x hx hdhi
    rw [Real.dist_eq] at hc
    linarith [le_abs_self (f (convexGridKnot a h (i + 1)) - f x)]
  exact ⟨grid_hinge_ge_local f hh htop hi hlo hhi hf,
    convexGridHinge_le_of_cell_values _ a hh hi hlo hhi hvlo hvhi⟩

end SpringerLean
