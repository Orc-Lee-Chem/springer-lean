import SpringerLean.Round30TailTranslate

open MeasureTheory Set

namespace SpringerLean

/-- A vertical shift by at most m sends the complement of [-2m,2m]
inside the complement of [-m,m]. -/
theorem shifted_large_interval_compl_subset_small
    (m ε : ℝ) (hε : |ε| ≤ m) :
    (Icc (-(2 * m) + ε) (2 * m + ε))ᶜ ⊆
      (Icc (-m) m)ᶜ := by
  intro y hy
  by_contra hsmall
  have hsmall' : y ∈ Icc (-m) m := by simpa using hsmall
  apply hy
  have hεbounds := abs_le.mp hε
  exact ⟨by linarith [hsmall'.1, hεbounds.2],
    by linarith [hsmall'.2, hεbounds.1]⟩

/-- Uniform absolute-tail domination after any vertical displacement of
magnitude at most m. This is the measure-theoretic input for angular tails. -/
theorem integral_shifted_outer_tail_abs_le
    (f : ℝ → ℝ) (hf : Integrable f) (m ε : ℝ) (hε : |ε| ≤ m) :
    (∫ t in (Icc (-(2 * m)) (2 * m))ᶜ, |f (t + ε)|) ≤
      (∫ t in (Icc (-m) m)ᶜ, |f t|) := by
  have hshift := integral_compl_Icc_comp_add_right (fun y : ℝ => |f y|) (2 * m) ε
  rw [hshift]
  apply setIntegral_mono_set hf.abs.integrableOn
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (Filter.Eventually.of_forall ?_)
  intro y hy
  exact shifted_large_interval_compl_subset_small m ε hε hy

end SpringerLean