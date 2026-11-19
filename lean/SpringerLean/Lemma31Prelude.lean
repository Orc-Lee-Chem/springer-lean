import SpringerLean.GeneralArea
import Mathlib.Analysis.Normed.Group.Tannery

open Filter
open scoped Topology

namespace SpringerLean

/-- The finite area theorem supplies the weighted coefficient summability
needed for the `g' ∈ L²` approximation stage of Lemma 3.1. -/
theorem exteriorForwardCoeff_weighted_summable
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Summable (fun j : ℕ =>
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) := by
  let w : ℕ → ℝ := fun j =>
    (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2
  have hw : 0 ≤ w := by
    intro j
    dsimp [w]
    positivity
  apply summable_of_sum_le hw
  intro s
  let N : ℕ := s.sup id
  have hsubset : s.erase 0 ⊆ Finset.Icc 1 N := by
    intro j hj
    obtain ⟨hj0, hjs⟩ := Finset.mem_erase.mp hj
    apply Finset.mem_Icc.mpr
    constructor
    · omega
    · exact Finset.le_sup (f := id) hjs
  have hbound :
      (∑ j ∈ s.erase 0, w j) ≤
      ∑ j ∈ Finset.Icc 1 N, w j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro j hj _
    exact hw j
  calc
    (∑ j ∈ s, w j) = ∑ j ∈ s.erase 0, w j := by
      exact (Finset.sum_erase s (by simp [w])).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 N, w j := hbound
    _ ≤ 1 := exteriorForwardCoeff_finite_area F hc N

/-- The weighted coefficient energy has total mass at most one. -/
theorem exteriorForwardCoeff_weighted_tsum_le_one
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    (∑' j : ℕ,
      (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) ≤ 1 := by
  let w : ℕ → ℝ := fun j =>
    (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2
  have hw : 0 ≤ w := by
    intro j
    dsimp [w]
    positivity
  apply Real.tsum_le_of_sum_le hw
  intro s
  let N : ℕ := s.sup id
  have hsubset : s.erase 0 ⊆ Finset.Icc 1 N := by
    intro j hj
    obtain ⟨hj0, hjs⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, Finset.le_sup (f := id) hjs⟩
  calc
    (∑ j ∈ s, w j) = ∑ j ∈ s.erase 0, w j := by
      exact (Finset.sum_erase s (by simp [w])).symm
    _ ≤ ∑ j ∈ Finset.Icc 1 N, w j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro j hj _
      exact hw j
    _ ≤ 1 := exteriorForwardCoeff_finite_area F hc N

/-- The weighted derivative-mode energy of radial dilations converges to
the full energy as the dilation parameter approaches one from below. -/
theorem exteriorForwardCoeff_dilated_energy_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    Tendsto
      (fun s : ℝ => ∑' j : ℕ,
        ((j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2) *
          s ^ (2 * j))
      (𝓝[<] (1 : ℝ))
      (𝓝 (∑' j : ℕ,
        (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2)) := by
  let w : ℕ → ℝ := fun j =>
    (j : ℝ) * ‖exteriorForwardCoeff F j‖ ^ 2
  have hw : ∀ j, 0 ≤ w j := by
    intro j
    dsimp [w]
    positivity
  have hsum : Summable w := exteriorForwardCoeff_weighted_summable F hc
  have hfilter : (𝓝[<] (1 : ℝ)) ≤ 𝓝 (1 : ℝ) := nhdsWithin_le_nhds
  have hterm (j : ℕ) : Tendsto
      (fun s : ℝ => w j * s ^ (2 * j))
      (𝓝[<] (1 : ℝ)) (𝓝 (w j)) := by
    have hs : Tendsto (fun s : ℝ => s) (𝓝[<] (1 : ℝ)) (𝓝 1) :=
      tendsto_id.mono_left hfilter
    simpa using (tendsto_const_nhds.mul (hs.pow (2 * j)))
  have hbound : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ),
      ∀ j, ‖w j * s ^ (2 * j)‖ ≤ w j := by
    have h0 : ∀ᶠ s : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ s :=
      hfilter (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hs1 j
    have hsle : s ≤ 1 := hs1.le
    have hpow : 0 ≤ s ^ (2 * j) := pow_nonneg hs0 _
    have hpowle : s ^ (2 * j) ≤ 1 := by
      simpa using (pow_le_pow_left₀ hs0 hsle (2 * j))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw j) hpow)]
    exact mul_le_of_le_one_right (hw j) hpowle
  have h := tendsto_tsum_of_dominated_convergence hsum hterm hbound
  simpa [w] using h

end SpringerLean
