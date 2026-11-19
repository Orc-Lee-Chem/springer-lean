import SpringerLean.Round27TailL1
import SpringerLean.Round27Tail
import Mathlib.Topology.UniformSpace.Dini

open MeasureTheory Set Filter
open scoped Topology

namespace SpringerLean

/-- Restricting a uniformly L1-Lipschitz family to a measurable set and
integrating its absolute value preserves the same Lipschitz constant. -/
theorem abs_setIntegral_lipschitz_of_L1
    (f : ℝ → ℝ → ℝ) (L : ℝ)
    (hInt : ∀ a, Integrable (f a))
    (hL1 : ∀ a b, (∫ y : ℝ, |f a y - f b y|) ≤ L * |a - b|)
    (S : Set ℝ) (a b : ℝ) :
    |(∫ y in S, |f a y|) - (∫ y in S, |f b y|)| ≤ L * |a - b| := by
  have ha := (hInt a).abs
  have hb := (hInt b).abs
  have hd := ((hInt a).sub (hInt b)).abs
  have hda := (ha.sub hb).abs
  calc
    |(∫ y in S, |f a y|) - (∫ y in S, |f b y|)| =
      |(∫ y in S, |f a y| - |f b y|)| := by
        rw [integral_sub ha.integrableOn hb.integrableOn]
    _ ≤ ∫ y in S, abs (abs (f a y) - abs (f b y)) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y in S, |f a y - f b y| := by
      apply integral_mono_ae hda.integrableOn hd.integrableOn
      filter_upwards with y
      exact abs_abs_sub_abs_le_abs_sub (f a y) (f b y)
    _ ≤ ∫ y : ℝ, |f a y - f b y| :=
      setIntegral_le_integral hd (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    _ ≤ L * |a - b| := hL1 a b

/-- For the actual paper potential, its absolute compensated tail tends to
zero uniformly as the horizontal coordinate ranges over any compact set. -/
theorem regularExterior_vertical_difference_abs_tail_uniformOn
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (ξ : ℂ) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun (n : ℕ) (a : ℝ) =>
        ∫ y in (Icc (-(n : ℝ)) (n : ℝ))ᶜ,
          |regularExteriorVerticalPotentialDifference F s ξ a y|)
      (fun _ => (0 : ℝ)) atTop K := by
  let f : ℝ → ℝ → ℝ := regularExteriorVerticalPotentialDifference F s ξ
  let A : ℕ → ℝ → ℝ := fun n a =>
    ∫ y in (Icc (-(n : ℝ)) (n : ℝ))ᶜ, |f a y|
  have hInt (a : ℝ) : Integrable (f a) :=
    regularExteriorVerticalPotentialDifference_integrable F hc hs0 hs1 ξ a
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hL1 (a b : ℝ) :
      (∫ y : ℝ, |f a y - f b y|) ≤ 2 * Real.pi * |a - b| :=
    regularExterior_vertical_difference_L1_lipschitz_horizontal
      F hc hs0 hs1 ξ a b
  have hcont (n : ℕ) : Continuous (A n) := by
    let c : NNReal := ⟨2 * Real.pi, hpi⟩
    have hlip : LipschitzWith c (A n) := by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simp only [Real.dist_eq, NNReal.coe_mk]
      exact abs_setIntegral_lipschitz_of_L1 f (2 * Real.pi)
        hInt hL1 _ a b
    exact hlip.continuous
  have hanti (a : ℝ) : Antitone (fun n => A n a) := by
    intro n m hnm
    dsimp [A]
    apply setIntegral_mono_set (hInt a).abs.integrableOn
      (Filter.Eventually.of_forall fun _ => abs_nonneg _) (Filter.Eventually.of_forall ?_)
    intro y hy
    have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    intro hyn
    apply hy
    exact ⟨by linarith [hyn.1], by linarith [hyn.2]⟩
  have hpoint (a : ℝ) : Tendsto (fun n => A n a) atTop (𝓝 0) := by
    exact integrable_symmetric_complement_tail_tendsto_zero (hInt a).abs
  exact Antitone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun n => (hcont n).continuousOn)
    (fun a _ => hanti a)
    continuous_const.continuousOn
    (fun a _ => hpoint a)

end SpringerLean