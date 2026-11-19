import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped BigOperators Interval

namespace SpringerLean

/-- Uniform Riemann sums for a continuous family of real integrands
parametrized by a compact metric space. The nodes are the left
endpoints of equal subintervals. -/
theorem exists_uniform_interval_samples {X : Type*} [MetricSpace X]
    (K : Set X) (hK : IsCompact K) (a b : ℝ) (hab : a < b)
    (H : X × ℝ → ℝ) (hH : ContinuousOn H (K ×ˢ Icc a b))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ K,
      |(∫ t in a..b, H (x,t)) -
        ((b-a)/(n:ℝ)) * ∑ i ∈ Finset.range n, H (x, a + ((b-a)/(n:ℝ)) * i)|
      ≤ ε * (b-a) := by
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod isCompact_Icc).uniformContinuousOn_of_continuous hH) ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt ((b-a)/δ)
  have hnpos : 0 < n := by
    have : 0 < (n:ℝ) := (div_pos (sub_pos.mpr hab) hδ).trans hn
    exact_mod_cast this
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hnpos
  let Δ := (b-a)/(n:ℝ)
  have hΔ : 0 < Δ := div_pos (sub_pos.mpr hab) hnR
  have hΔδ : Δ < δ := (div_lt_iff₀ hnR).mpr (by
    have := (div_lt_iff₀ hδ).mp hn
    nlinarith)
  let τ (i : ℕ) := a + Δ * (i:ℝ)
  have h0 : τ 0 = a := by simp [τ]
  have htop : τ n = b := by
    dsimp [τ, Δ]
    field_simp
    <;> ring
  have hτ : Monotone τ := by
    intro i j hij
    have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hij' hΔ.le)
  have hstep (i : ℕ) : τ (i+1) - τ i = Δ := by
    simp only [τ, Nat.cast_add, Nat.cast_one]
    ring
  have hnΔ : (n:ℝ) * Δ = b-a := by dsimp [Δ]; field_simp
  refine ⟨n, hnpos, ?_⟩
  intro x hx
  have hslice : ContinuousOn (fun t => H (x,t)) (Icc a b) :=
    hH.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun _ ht => ⟨hx,ht⟩)
  have hmem (i : ℕ) (hi : i ≤ n) : τ i ∈ Icc a b := by
    constructor
    · simpa only [h0] using hτ (Nat.zero_le i)
    · simpa only [htop] using hτ hi
  have hlocal (i : ℕ) (hi : i < n) :
      |(∫ t in τ i..τ (i+1), H (x,t)) - Δ * H (x,τ i)| ≤ ε * Δ := by
    have hmono := hτ (Nat.le_succ i)
    have hcont : ContinuousOn (fun t => H (x,t)) (Icc (τ i) (τ (i+1))) :=
      hslice.mono (Icc_subset_Icc (hmem i hi.le).1 (hmem (i+1) hi).2)
    have hbound : ∀ t ∈ uIoc (τ i) (τ (i+1)), ‖H (x,t) - H (x,τ i)‖ ≤ ε := by
      intro t ht
      rw [uIoc_of_le hmono] at ht
      have htK : t ∈ Icc a b :=
        ⟨(hmem i hi.le).1.trans ht.1.le, ht.2.trans (hmem (i+1) hi).2⟩
      have hdist : dist (x,t) (x,τ i) < δ := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le),
          max_eq_right (sub_nonneg.mpr ht.1.le)]
        linarith [hstep i, ht.2]
      exact (hu (x,t) ⟨hx,htK⟩ (x,τ i) ⟨hx,hmem i hi.le⟩ hdist).le
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    have hint : IntervalIntegrable (fun t => H (x,t)) volume (τ i) (τ (i+1)) :=
      (show ContinuousOn (fun t => H (x,t)) (uIcc (τ i) (τ (i+1))) from
        by rwa [uIcc_of_le hmono]).intervalIntegrable
    rw [intervalIntegral.integral_sub hint
      (intervalIntegrable_const : IntervalIntegrable (fun _ => H (x,τ i)) volume (τ i) (τ (i+1))),
      intervalIntegral.integral_const, smul_eq_mul, hstep, abs_of_pos hΔ] at h
    simpa only [Real.norm_eq_abs] using h
  have hint (i : ℕ) (hi : i < n) : IntervalIntegrable (fun t => H (x,t)) volume (τ i) (τ (i+1)) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hτ (Nat.le_succ i))]
    exact hslice.mono (Icc_subset_Icc (hmem i hi.le).1 (hmem (i+1) hi).2)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [h0, htop] at hsum
  change |(∫ t in a..b, H (x,t)) - Δ * ∑ i ∈ Finset.range n, H (x,τ i)| ≤ _
  rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |(∫ t in τ i..τ (i+1), H (x,t)) - Δ * H (x,τ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, ε * Δ :=
      Finset.sum_le_sum fun i hi => hlocal i (Finset.mem_range.mp hi)
    _ = ε * (b-a) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_left_comm, hnΔ]

end SpringerLean
