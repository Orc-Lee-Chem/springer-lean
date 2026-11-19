import SpringerLean.Round787ChebyshevCandidateParity

namespace SpringerLean
open Polynomial

theorem monicChebyshevCandidate_comp_neg_X (n : ℕ) :
    (monicChebyshevCandidate n).comp (-X) =
      C ((n : ℤ).negOnePow : ℝ) * monicChebyshevCandidate n := by
  apply Polynomial.funext
  intro x
  simpa [eval_comp] using monicChebyshevCandidate_eval_neg n x

theorem monicChebyshevCandidate_roots_neg (n : ℕ) :
    (monicChebyshevCandidate n).roots.map (fun x => -x) =
      (monicChebyshevCandidate n).roots := by
  rw [← roots_comp_neg_X, monicChebyshevCandidate_comp_neg_X]
  apply roots_C_mul
  norm_num

/-- The candidate's complete root multiset has zero barycentric sum. -/
theorem monicChebyshevCandidate_roots_sum_zero (n : ℕ) :
    (monicChebyshevCandidate n).roots.sum = 0 := by
  have h := congrArg Multiset.sum (monicChebyshevCandidate_roots_neg n)
  rw [Multiset.sum_map_neg] at h
  simp only [Multiset.map_id'] at h
  linarith

end SpringerLean

#print axioms SpringerLean.monicChebyshevCandidate_roots_neg
#print axioms SpringerLean.monicChebyshevCandidate_roots_sum_zero
