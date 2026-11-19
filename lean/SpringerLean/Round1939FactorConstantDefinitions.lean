import SpringerLean.Round1938OddStarOmittedBounds
import Mathlib.Topology.Order.Compact

open Polynomial

namespace SpringerLean

/-- The actual uniform norm of a complex polynomial on a plane set. -/
noncomputable def continuumPolynomialNorm
    (K : Set ℂ) (P : ℂ[X]) : ℝ :=
  sSup ((fun z : ℂ => ‖P.eval z‖) '' K)

/-- The factor inequality with a specified constant, for every finite
family of actual complex polynomials. Zero factors cause no difficulty. -/
def FactorInequality (K : Set ℂ) (c : ℝ) : Prop :=
  ∀ (r : ℕ) (P : Fin r → ℂ[X]),
    (∏ i : Fin r, continuumPolynomialNorm K (P i)) ≤
      c ^ (∑ i : Fin r, (P i).natDegree) *
        continuumPolynomialNorm K (∏ i : Fin r, P i)

/-- The least admissible constant in the polynomial factor inequality.
Finiteness and positivity are separate theorems for nondegenerate continua. -/
noncomputable def factorConstant (K : Set ℂ) : ℝ :=
  sInf {c : ℝ | 0 ≤ c ∧ FactorInequality K c}

/-- A compact nonempty set has a point attaining each polynomial norm. -/
theorem continuumPolynomialNorm_attained
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (P : ℂ[X]) :
    ∃ z ∈ K, ∀ w ∈ K, ‖P.eval w‖ ≤ ‖P.eval z‖ := by
  have hcont : Continuous (fun z : ℂ => ‖P.eval z‖) := by
    fun_prop
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne hcont.continuousOn
  exact ⟨z, hz, fun w hw => hmax hw⟩

theorem continuumPolynomialNorm_eq_at_max
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (P : ℂ[X]) {z : ℂ} (hz : z ∈ K)
    (hmax : ∀ w ∈ K, ‖P.eval w‖ ≤ ‖P.eval z‖) :
    continuumPolynomialNorm K P = ‖P.eval z‖ := by
  unfold continuumPolynomialNorm
  apply le_antisymm
  · apply csSup_le (hne.image _)
    rintro y ⟨w, hw, rfl⟩
    exact hmax w hw
  · apply le_csSup
    · refine ⟨‖P.eval z‖, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      exact hmax w hw
    · exact ⟨z, hz, rfl⟩

theorem continuumPolynomialNorm_nonneg
    (K : Set ℂ) (hK : IsCompact K) (hne : K.Nonempty)
    (P : ℂ[X]) :
    0 ≤ continuumPolynomialNorm K P := by
  obtain ⟨z, hz, hmax⟩ := continuumPolynomialNorm_attained K hK hne P
  rw [continuumPolynomialNorm_eq_at_max K hK hne P hz hmax]
  exact norm_nonneg _

end SpringerLean

#print axioms SpringerLean.continuumPolynomialNorm_attained
#print axioms SpringerLean.continuumPolynomialNorm_eq_at_max
