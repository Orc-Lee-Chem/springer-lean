import SpringerLean.Round2058ConnectedShortChains
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Basic

open Set Metric Relation

namespace SpringerLean

/-- Reciprocal points where the distance from every pole in (K)
is large enough compared with the allowed chain step. This formula
includes zero, the reciprocal coordinate of infinity. -/
def reciprocalSeparation (K : Set ℂ) (ε : ℝ) : Set ℂ :=
  {u | ∀ a ∈ K, ε * ‖u‖ < ‖1 - a*u‖}

theorem zero_mem_reciprocalSeparation (K : Set ℂ) (ε : ℝ) :
    (0 : ℂ) ∈ reciprocalSeparation K ε := by
  intro a ha
  simp

private theorem reciprocalSeparation_ne_zero {K : Set ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) {u a : ℂ} (hu : u ∈ reciprocalSeparation K ε)
    (ha : a ∈ K) : 1 - a*u ≠ 0 :=
  norm_pos_iff.mp (lt_of_le_of_lt (mul_nonneg hε (norm_nonneg u)) (hu a ha))

private theorem reciprocal_ratio_mem_slitPlane {K : Set ℂ} {ε : ℝ}
    (hε : 0 < ε) {a b u : ℂ} (hb : b ∈ K)
    (hab : dist a b < ε) (hu : u ∈ reciprocalSeparation K ε) :
    (1 - a*u) / (1 - b*u) ∈ Complex.slitPlane := by
  have hb0 := reciprocalSeparation_ne_zero hε.le hu hb
  have heq : (1 - a*u) / (1 - b*u) = 1 + ((b-a)*u)/(1-b*u) := by
    calc
      _ = ((1-b*u) + (b-a)*u)/(1-b*u) := by congr 1; ring
      _ = _ := by rw [add_div, div_self hb0]
  rw [heq]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_div, norm_mul, div_lt_one (norm_pos_iff.mpr hb0)]
  have hdist : ‖b-a‖ ≤ ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hab.le
  exact (mul_le_mul_of_nonneg_right hdist (norm_nonneg u)).trans_lt (hu b hb)

private theorem reciprocal_ratio_local_log {K : Set ℂ} {ε : ℝ}
    (hε : 0 < ε) {a b : ℂ} (hb : b ∈ K) (hab : dist a b < ε) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (reciprocalSeparation K ε) ∧ L 0 = 0 ∧
      ∀ u ∈ reciprocalSeparation K ε,
        Complex.exp (L u) = (1-a*u)/(1-b*u) := by
  refine ⟨fun u => Complex.log ((1-a*u)/(1-b*u)), ?_, by simp, ?_⟩
  · intro u hu
    have han : AnalyticAt ℂ (fun v : ℂ => (1-a*v)/(1-b*v)) u :=
      (by fun_prop : AnalyticAt ℂ (fun v : ℂ => 1-a*v) u).div
        (by fun_prop) (reciprocalSeparation_ne_zero hε.le hu hb)
    exact han.clog (reciprocal_ratio_mem_slitPlane hε hb hab hu)
  · intro u hu
    exact Complex.exp_log (Complex.slitPlane_ne_zero
      (reciprocal_ratio_mem_slitPlane hε hb hab hu))

/-- Finite short chains inside the connected compact set give an
analytic logarithm of a root ratio on every uniformly separated
reciprocal region. The branch is zero at reciprocal infinity. -/
theorem reciprocal_ratio_analytic_log_on_separation
    (K : Set ℂ) (hK : IsPreconnected K) (ε : ℝ) (hε : 0 < ε)
    (a b : ℂ) (ha : a ∈ K) (hb : b ∈ K) :
    ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (reciprocalSeparation K ε) ∧ L 0 = 0 ∧
      ∀ u ∈ reciprocalSeparation K ε,
        Complex.exp (L u) = (1-a*u)/(1-b*u) := by
  have : PreconnectedSpace K := Subtype.preconnectedSpace hK
  let x : K := ⟨a, ha⟩
  suffices ∀ y : K, ReflTransGen (fun x y : K => dist x y < ε) x y →
      ∃ L : ℂ → ℂ, AnalyticOnNhd ℂ L (reciprocalSeparation K ε) ∧ L 0 = 0 ∧
      ∀ u ∈ reciprocalSeparation K ε,
        Complex.exp (L u) = (1-(x : ℂ)*u)/(1-(y : ℂ)*u) by
    let y : K := ⟨b, hb⟩
    exact this y (preconnected_reflTransGen_dist_lt x y hε)
  intro y hchain
  induction hchain with
  | refl =>
    refine ⟨fun _ => 0, analyticOnNhd_const, rfl, ?_⟩
    intro u hu
    rw [Complex.exp_zero, div_self (reciprocalSeparation_ne_zero hε.le hu x.2)]
  | @tail z w _ hstep ih =>
    obtain ⟨L, hL, hL0, hLexp⟩ := ih
    obtain ⟨M, hM, hM0, hMexp⟩ := reciprocal_ratio_local_log hε w.2 hstep
    refine ⟨fun u => L u + M u, hL.add hM, by simp [hL0, hM0], ?_⟩
    intro u hu
    rw [Complex.exp_add, hLexp u hu, hMexp u hu]
    exact div_mul_div_cancel₀ (reciprocalSeparation_ne_zero hε.le hu z.2)

end SpringerLean
