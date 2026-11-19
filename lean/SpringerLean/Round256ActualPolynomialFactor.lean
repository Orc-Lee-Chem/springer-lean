import SpringerLean.Round255ActualFaberNormalization
import SpringerLean.Round88FaberActual

namespace SpringerLean
open PowerSeries

noncomputable def polynomialReciprocalFactor
    (F : ℂ → ℂ) (P : Polynomial ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    P.coeff j * (u ^ (n - j) * exteriorPhi F u ^ j)

theorem polynomialReciprocalFactor_eq_reciprocal_eval
    (F : ℂ → ℂ) (P : Polynomial ℂ) (n : ℕ)
    (hP : P.natDegree ≤ n) {u : ℂ} (hu : u ≠ 0) :
    u ^ n * P.eval (F u⁻¹) = polynomialReciprocalFactor F P n u := by
  rw [Polynomial.eval_eq_sum_range' (n := n + 1) (by omega),
    Finset.mul_sum, polynomialReciprocalFactor]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
  rw [exteriorF_reciprocal_phi F hu, mul_pow, inv_pow, pow_sub₀ u hu hjn]
  ring

theorem polynomialReciprocalFactor_analyticAt
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P : Polynomial ℂ) (n : ℕ) :
    AnalyticAt ℂ (polynomialReciprocalFactor F P n) 0 := by
  have hφ := exteriorPhi_analyticAt F hc.2.2
  unfold polynomialReciprocalFactor
  fun_prop

theorem actualTaylorSeries_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) :
    actualTaylorSeries (fun u => ∑ i ∈ s, f i u) =
      ∑ i ∈ s, actualTaylorSeries (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using actualTaylorSeries_const_mul (0 : ℂ) (fun u => u)
  | @insert i s hi ih =>
      have hfi := hf i (by simp)
      have hfs : ∀ j ∈ s, AnalyticAt ℂ (f j) 0 := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum : AnalyticAt ℂ (fun u => ∑ j ∈ s, f j u) 0 := by
        fun_prop
      simp only [Finset.sum_insert hi]
      rw [actualTaylorSeries_add _ _ hfi hsum, ih hfs]

/-- The finite reciprocal factor's Taylor coefficients are the actual
derivative coefficients, identified with the independent formal factor. -/
theorem polynomialReciprocalFactor_actualTaylorSeries
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (P : Polynomial ℂ) (n : ℕ) :
    actualTaylorSeries (polynomialReciprocalFactor F P n) =
      polynomialFormalReciprocalFactor
        (formalExteriorPhi (exteriorFormalForward F)) P n := by
  have hφ := exteriorPhi_analyticAt F hc.2.2
  unfold polynomialReciprocalFactor polynomialFormalReciprocalFactor
  rw [actualTaylorSeries_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [actualTaylorSeries_const_mul]
    rw [actualTaylorSeries_mul
        (fun u : ℂ => u ^ (n - j))
        (fun u : ℂ => exteriorPhi F u ^ j) (by fun_prop) (by fun_prop),
      actualTaylorSeries_monomial,
      actualTaylorSeries_pow _ hφ j,
      exteriorPhi_actualTaylorSeries F hc]
    ring
  · intro j hj
    fun_prop

end SpringerLean
