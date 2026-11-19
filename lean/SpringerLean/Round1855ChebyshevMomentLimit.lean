import SpringerLean.Round1854MidpointIntegralLimit
import SpringerLean.Round1852ChebyshevRealMomentTransfer
import SpringerLean.Round774ChebyshevScaleLimit

open MeasureTheory Filter Finset Polynomial
open scoped Topology

namespace SpringerLean

/-- The arcsine p-moment in a nonsingular angle coordinate. -/
noncomputable def arcsineRadialMomentIntegral (p : ℝ) : ℝ :=
  (2 : ℝ) ^ p * ∫ x in (0 : ℝ)..1, |Real.cos (Real.pi * x)| ^ p

theorem chebyshev_abs_rpow_grid_average_tendsto (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ range n, |chebyshevZeroGrid n i| ^ p) / n)
      atTop (𝓝 (∫ x in (0 : ℝ)..1, |Real.cos (Real.pi * x)| ^ p)) := by
  have hf : Continuous (fun x : ℝ => |Real.cos (Real.pi * x)| ^ p) :=
    Real.continuous_rpow_const hp.le |>.comp (by fun_prop)
  have hh := continuousOn_midpoint_average_tendsto
    (fun x : ℝ => |Real.cos (Real.pi * x)| ^ p) hf.continuousOn
  apply hh.congr'
  filter_upwards with n
  apply congrArg (fun x : ℝ => x / (n : ℝ))
  apply Finset.sum_congr rfl
  intro i _
  have hangle : (2 * (i : ℝ) + 1) * Real.pi / (2 * n) =
      Real.pi * (((i : ℝ) + 1 / 2) / n) := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
      <;> ring
  simp only [chebyshevZeroGrid, hangle]

/-- The capacity-normalized monic Chebyshev polynomials attain the
arcsine moment in the limit for every real p>0.  No real-p upper bound
for general exterior maps is used. -/
theorem monicChebyshevCandidate_abs_rpow_moment_tendsto
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n : ℕ =>
      (((monicChebyshevCandidate n).roots.map (fun x => |x| ^ p)).sum) / n)
      atTop (𝓝 (arcsineRadialMomentIntegral p)) := by
  have hscale : Tendsto (fun n : ℕ => ((monicChebyshevScale n)⁻¹) ^ p)
      atTop (𝓝 ((2 : ℝ) ^ p)) :=
    (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp
      monicChebyshevScale_inv_tendsto_two
  have hlim := hscale.mul (chebyshev_abs_rpow_grid_average_tendsto p hp)
  apply hlim.congr'
  filter_upwards with n
  have hs : 0 < (monicChebyshevScale n)⁻¹ :=
    inv_pos.2 (Real.rpow_pos_of_pos (by norm_num) _)
  have hmul (x : ℝ) : |(monicChebyshevScale n)⁻¹ * x| ^ p =
      ((monicChebyshevScale n)⁻¹) ^ p * |x| ^ p := by
    rw [abs_mul, abs_of_pos hs, Real.mul_rpow hs.le (abs_nonneg x)]
  rw [monicChebyshevCandidate_roots, Multiset.map_map]
  rw [chebyshev_test_sum_eq_grid]
  simp only [Function.comp_def]
  simp_rw [hmul]
  rw [← Finset.mul_sum]
  ring

end SpringerLean

#print axioms SpringerLean.chebyshev_abs_rpow_grid_average_tendsto
#print axioms SpringerLean.monicChebyshevCandidate_abs_rpow_moment_tendsto
