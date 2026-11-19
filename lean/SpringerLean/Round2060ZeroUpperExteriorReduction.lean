import SpringerLean.Round2051PolynomialRootBoundaryComparison
import SpringerLean.Round2057DerivativeRootMoments
import SpringerLean.Round1985ZeroMomentSupremumReduction

open Polynomial

namespace SpringerLean

/-- The remaining analytic construction for arbitrary normalized
connected polynomial lemniscates. Existence must be proved before
using the unrestricted conclusions of Proposition 9.2. -/
def ConnectedLemniscateExteriorExistence : Prop :=
  ∀ Q : ℂ[X], Q.Monic → 0 < Q.natDegree → Q.roots.sum = 0 →
    IsConnected {z : ℂ | ‖Q.eval z‖ ≤ 1} →
    ∃ F : ℂ → ℂ, CenteredExteriorUnivalent F ∧
      (∀ w ∈ exteriorDisk, Q.eval (F w) = w ^ Q.natDegree)

/-- The general strict upper for the actual polynomial and all
derivative orders, conditional on only the exterior construction. -/
theorem originalPolynomial_derivative_root_power_mean_strict_of_exterior
    (hexterior : ConnectedLemniscateExteriorExistence)
    (P : ℂ[X]) (hP : 0 < P.natDegree) (t : ℝ) (ht : 0 < t)
    (hK : IsConnected {w : ℂ | ‖P.eval w‖ ≤ t})
    (j : ℕ) (hj : j < P.natDegree) (p : ℝ) (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    ((((derivative^[j]) P).roots.map
      (fun w : ℂ => ‖(w - polynomialZeroCentroid P) /
        (polynomialLemniscateRadius P t : ℂ)‖ ^ p)).sum) /
      ((P.natDegree - j : ℕ) : ℝ) < slitRadialMomentConstant p := by
  let Q := polynomialAffineMonic P (polynomialZeroCentroid P)
    (polynomialLemniscateRadius P t)
  obtain ⟨_, hmonic, hdeg, hsum, hconn⟩ :=
    polynomialLemniscate_normalized_centered_connected P hP t ht hK
  have hdeg' : Q.natDegree = P.natDegree := hdeg
  have hpos : 0 < Q.natDegree := hdeg' ▸ hP
  have hj' : j < Q.natDegree := hdeg' ▸ hj
  obtain ⟨F, hF, hidentity⟩ := hexterior Q hmonic hpos hsum hconn
  have hupper := (polynomial_iterated_derivative_root_power_mean_le Q j hj' p
    (by linarith)).trans_lt
      (polynomial_root_power_mean_strict_of_exterior_identity Q hmonic hpos
        F hF hidentity p hp4 hp8)
  rwa [hdeg', originalPolynomial_derivative_root_power_mean_normalization P hP t ht j hj p]
    at hupper

/-- The supremum for the normalized admissible class follows from the
same exterior construction and the existing Chebyshev witnesses. -/
theorem connectedLemniscateDerivativeZeroMoments_csSup_of_exterior
    (hexterior : ConnectedLemniscateExteriorExistence) (j : ℕ) (p : ℝ)
    (hp4 : 4 ≤ p) (hp8 : p ≤ 8) :
    sSup (connectedLemniscateDerivativeZeroMoments j p) = slitRadialMomentConstant p := by
  apply connectedLemniscateDerivativeZeroMoments_csSup_of_upper j p (by linarith)
  rintro _ ⟨Q, hQ, hj, hsum, hconn, rfl⟩
  have hpos : 0 < Q.natDegree := (Nat.zero_le j).trans_lt hj
  obtain ⟨F, hF, hidentity⟩ := hexterior Q hQ hpos hsum hconn
  apply le_of_lt
  exact (polynomial_iterated_derivative_root_power_mean_le Q j hj p
    (by linarith)).trans_lt
      (polynomial_root_power_mean_strict_of_exterior_identity Q hQ hpos
        F hF hidentity p hp4 hp8)

end SpringerLean
