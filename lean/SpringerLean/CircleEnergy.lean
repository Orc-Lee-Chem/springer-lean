import SpringerLean.AnnulusArea
import Mathlib.Analysis.Fourier.AddCircle

open MeasureTheory
open AddCircle
open scoped ComplexConjugate

namespace SpringerLean


private theorem single_complex_one_apply (m n : ℤ) :
    Pi.single (M := fun _ : ℤ => ℂ) m (1 : ℂ) n =
      if m = n then 1 else 0 := by
  by_cases h : m = n <;> simp [h]

/-- Distinct integer Fourier modes on the normalized circle are orthogonal. -/
theorem fourier_pair_integral (T : ℝ) [Fact (0 < T)] (m n : ℤ) :
    (∫ θ : AddCircle T,
      fourier m θ * star (fourier n θ) ∂(@haarAddCircle T _)) =
      if m = n then 1 else 0 := by
  calc
    (∫ θ : AddCircle T,
      fourier m θ * star (fourier n θ) ∂(@haarAddCircle T _)) =
        fourierCoeff (T := T) (fourier (T := T) m) n := by
          simp [fourierCoeff, smul_eq_mul, mul_comm]
    _ = Pi.single (M := fun _ : ℤ => ℂ) m (1 : ℂ) n :=
      congrFun (fourierCoeff_fourier (T := T) m) n
    _ = if m = n then 1 else 0 := single_complex_one_apply m n

/-- A finite Fourier polynomial, viewed as an actual function on the circle. -/
noncomputable def finiteFourierPolynomial (T : ℝ) (s : Finset ℤ)
    (c : ℤ → ℂ) (θ : AddCircle T) : ℂ :=
  ∑ n ∈ s, c n * fourier n θ

theorem finiteFourierPolynomial_complex_energy
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ θ : AddCircle T,
      finiteFourierPolynomial T s c θ *
        star (finiteFourierPolynomial T s c θ)
      ∂(@haarAddCircle T _)) =
      ∑ n ∈ s, c n * star (c n) := by
  have hpoint (θ : AddCircle T) :
      finiteFourierPolynomial T s c θ *
          star (finiteFourierPolynomial T s c θ) =
        ∑ n ∈ s, ∑ m ∈ s,
          (c n * star (c m)) *
            (fourier n θ * star (fourier m θ)) := by
    unfold finiteFourierPolynomial
    simp_rw [star_sum, star_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    congr 1
    ext n
    congr 1
    ext m
    ring
  have hint (n m : ℤ) :
      Integrable (fun θ : AddCircle T =>
        (c n * star (c m)) * (fourier n θ * star (fourier m θ)))
        (@haarAddCircle T _) := by
    have hcont : Continuous (fun θ : AddCircle T =>
        (c n * star (c m)) * (fourier n θ * star (fourier m θ))) := by
      fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ θ : AddCircle T,
      finiteFourierPolynomial T s c θ *
        star (finiteFourierPolynomial T s c θ)
      ∂(@haarAddCircle T _)) =
      ∫ θ : AddCircle T,
        ∑ n ∈ s, ∑ m ∈ s,
          (c n * star (c m)) *
            (fourier n θ * star (fourier m θ))
        ∂(@haarAddCircle T _) := by simp only [hpoint]
    _ = ∑ n ∈ s, ∑ m ∈ s,
        (c n * star (c m)) *
          (if n = m then 1 else 0) := by
      rw [integral_finsetSum]
      · congr 1
        ext n
        rw [integral_finsetSum]
        · congr 1
          ext m
          rw [integral_const_mul, fourier_pair_integral]
        · intro m hm
          exact hint n m
      · intro n hn
        convert integrable_finsetSum' s (fun m hm => hint n m) using 1
        funext θ
        simp only [Finset.sum_apply]
    _ = ∑ n ∈ s, c n * star (c n) := by
      simp

/-- Finite Parseval identity for a Fourier polynomial on normalized Haar
measure. No infinite Fourier series or convergence theorem is used. -/
theorem finiteFourierPolynomial_energy
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ θ : AddCircle T,
      ‖finiteFourierPolynomial T s c θ‖ ^ 2
      ∂(@haarAddCircle T _)) =
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (∫ θ : AddCircle T,
        ((‖finiteFourierPolynomial T s c θ‖ ^ 2 : ℝ) : ℂ)
        ∂(@haarAddCircle T _)) =
      ∫ θ : AddCircle T,
        finiteFourierPolynomial T s c θ *
          star (finiteFourierPolynomial T s c θ)
        ∂(@haarAddCircle T _) := by
      congr 1
      funext θ
      change ((‖finiteFourierPolynomial T s c θ‖ ^ 2 : ℝ) : ℂ) =
        finiteFourierPolynomial T s c θ *
          conj (finiteFourierPolynomial T s c θ)
      rw [Complex.mul_conj']
      norm_cast
    _ = ∑ n ∈ s, c n * star (c n) :=
      finiteFourierPolynomial_complex_energy T s c
    _ = ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      congr 1
      ext n
      change c n * conj (c n) = (‖c n‖ : ℂ) ^ 2
      rw [Complex.mul_conj']

end SpringerLean
