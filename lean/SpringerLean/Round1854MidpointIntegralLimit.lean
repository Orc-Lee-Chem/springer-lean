import SpringerLean.Round1853TaggedIntegralError
import Mathlib.Topology.UniformSpace.HeineCantor

open MeasureTheory Filter Set Finset
open scoped Topology

namespace SpringerLean

/-- Midpoint Riemann sums for a continuous real function, using only
finite interval decompositions and uniform continuity on [0,1]. -/
theorem continuousOn_midpoint_average_tendsto
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ range n, f (((i : ℝ) + 1 / 2) / n)) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, f x)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / δ) (1 : ℝ))
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith [le_max_right (1 / δ) (1 : ℝ)]
  have hlarge : 1 / δ < (n : ℝ) :=
    (lt_of_le_of_lt (le_max_left _ _) hN).trans_le hNn
  have hmesh : 1 / (n : ℝ) < δ := by
    have hh := (div_lt_iff₀ hδ).1 hlarge
    apply (div_lt_iff₀ hn0).2
    nlinarith
  let a : ℕ → ℝ := fun i => (i : ℝ) / n
  let tag : ℕ → ℝ := fun i => ((i : ℝ) + 1 / 2) / n
  have horder (i : ℕ) (_ : i < n) : a i ≤ a (i + 1) := by
    dsimp only [a]
    apply div_le_div_of_nonneg_right _ hn0.le
    exact_mod_cast Nat.le_succ i
  have hwidth (i : ℕ) : a (i + 1) - a i = 1 / (n : ℝ) := by
    dsimp only [a]
    push_cast
    ring
  have hcell (i : ℕ) (hi : i < n) : Icc (a i) (a (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hi)
    apply Set.Icc_subset_Icc
    · dsimp only [a]
      positivity
    · dsimp only [a]
      push_cast
      exact (div_le_one hn0).2 hi'
  have htag (i : ℕ) : tag i ∈ Icc (a i) (a (i + 1)) := by
    dsimp only [a, tag]
    push_cast
    constructor <;> apply div_le_div_of_nonneg_right _ hn0.le <;> linarith
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable f volume (a i) (a (i + 1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (horder i hi)]
    exact hf.mono (hcell i hi)
  have hosc (i : ℕ) (hi : i < n) (x : ℝ) (hx : x ∈ Icc (a i) (a (i + 1))) :
      |f (tag i) - f x| ≤ ε / 2 := by
    have ht := htag i
    have hd : dist (tag i) x ≤ 1 / (n : ℝ) := by
      rw [Real.dist_eq]
      apply abs_le.2
      have hw := hwidth i
      constructor <;> linarith [ht.1, ht.2, hx.1, hx.2]
    have hh := huc (tag i) (hcell i hi ht) x (hcell i hi hx) (hd.trans_lt hmesh)
    exact (by simpa only [Real.dist_eq] using hh.le)
  have hbound := tagged_interval_sum_error f a tag n (ε / 2) horder hint hosc
  have hsum : (∑ i ∈ range n, (a (i + 1) - a i) * f (tag i)) =
      (∑ i ∈ range n, f (tag i)) / n := by
    simp_rw [hwidth]
    rw [← Finset.mul_sum]
    ring
  have ha0 : a 0 = 0 := by simp [a]
  have han : a n = 1 := div_self hn0.ne'
  rw [hsum, ha0, han] at hbound
  rw [Real.dist_eq]
  change |(∑ i ∈ range n, f (tag i)) / n - (∫ x in (0 : ℝ)..1, f x)| < ε
  exact hbound.trans_lt (by linarith)

end SpringerLean

#print axioms SpringerLean.continuousOn_midpoint_average_tendsto
