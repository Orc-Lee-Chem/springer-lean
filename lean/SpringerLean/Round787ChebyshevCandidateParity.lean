import SpringerLean.Round774ChebyshevScaleLimit

namespace SpringerLean
open Polynomial

/-- The scaled monic family retains the parity of the underlying
Chebyshev polynomial. This is the first centering input for Proposition 9.2. -/
theorem monicChebyshevCandidate_eval_neg (n : ℕ) (x : ℝ) :
    (monicChebyshevCandidate n).eval (-x) =
      (n : ℤ).negOnePow * (monicChebyshevCandidate n).eval x := by
  simp only [monicChebyshevCandidate, eval_comp, eval_mul,
    eval_C, eval_X, mul_neg]
  exact Chebyshev.T_eval_neg ℝ (n : ℤ) (monicChebyshevScale n * x)

end SpringerLean

#print axioms SpringerLean.monicChebyshevCandidate_eval_neg
