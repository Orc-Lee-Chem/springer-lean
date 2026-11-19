import SpringerLean.Round82BoundaryFourierPrelude
import SpringerLean.CircleEnergy

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace SpringerLean

/-- Bilinear finite Fourier orthogonality on the normalized circle. Unlike
Parseval, the two coefficient families may differ. This is the finite
identity needed for weighted signed boundary area. -/
theorem finiteFourierPolynomial_pairing
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c d : ℤ → ℂ) :
    (∫ θ : AddCircle T,
      finiteFourierPolynomial T s c θ *
        star (finiteFourierPolynomial T s d θ)
      ∂@haarAddCircle T _) =
      ∑ n ∈ s, c n * star (d n) := by
  classical
  have hpoint (θ : AddCircle T) :
      finiteFourierPolynomial T s c θ *
          star (finiteFourierPolynomial T s d θ) =
        ∑ n ∈ s, ∑ m ∈ s,
          (c n * star (d m)) *
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
        (c n * star (d m)) *
          (fourier n θ * star (fourier m θ)))
        (@haarAddCircle T _) := by
    have hcont : Continuous (fun θ : AddCircle T =>
        (c n * star (d m)) *
          (fourier n θ * star (fourier m θ))) := by fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ θ : AddCircle T,
      finiteFourierPolynomial T s c θ *
        star (finiteFourierPolynomial T s d θ)
      ∂@haarAddCircle T _) =
      ∫ θ : AddCircle T,
        ∑ n ∈ s, ∑ m ∈ s,
          (c n * star (d m)) *
            (fourier n θ * star (fourier m θ))
        ∂@haarAddCircle T _ := by simp only [hpoint]
    _ = ∑ n ∈ s, ∑ m ∈ s,
        (c n * star (d m)) *
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
    _ = ∑ n ∈ s, c n * star (d n) := by simp


/-- The weighted diagonal energy is signed by the integer frequency.
This algebraic form is later identified with an oriented Green boundary. -/
theorem finiteFourierPolynomial_signed_pairing
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ θ : AddCircle T,
      finiteFourierPolynomial T s c θ *
        star (finiteFourierPolynomial T s
          (fun n => (n : ℂ) * c n) θ)
      ∂@haarAddCircle T _) =
      ∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
  rw [finiteFourierPolynomial_pairing]
  apply Finset.sum_congr rfl
  intro n hn
  change c n * conj ((n : ℂ) * c n) = _
  rw [map_mul]
  simp only [map_intCast]
  change c n * ((n : ℂ) * conj (c n)) = _
  calc
    _ = (n : ℂ) * (c n * conj (c n)) := by ring
    _ = _ := by rw [Complex.mul_conj']; push_cast; rfl

/-- Differentiate a finite Fourier polynomial after pulling it back to a
real angle. The frequency factor is kept explicit for signed area. -/
theorem finiteFourierPolynomial_hasDerivAt_real
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) (θ : ℝ) :
    HasDerivAt
      (fun t : ℝ => finiteFourierPolynomial T s c (t : AddCircle T))
      (∑ n ∈ s,
        c n * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) /
          (T : ℂ) * fourier n (θ : AddCircle T))) θ := by
  have hsum : HasDerivAt
      (∑ n ∈ s, fun t : ℝ => c n * fourier n (t : AddCircle T))
      (∑ n ∈ s,
        c n * (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) /
          (T : ℂ) * fourier n (θ : AddCircle T))) θ := by
    apply HasDerivAt.sum
    intro n hn
    simpa only [] using (hasDerivAt_fourier T n θ).const_mul (c n)
  change HasDerivAt (fun t : ℝ =>
    ∑ n ∈ s, c n * fourier n (t : AddCircle T)) _ θ
  convert hsum using 1
  funext t
  simp only [Finset.sum_apply]

/-- Transfer finite Fourier orthogonality from normalized Haar measure
to the oriented real-angle interval of length `T`. -/
theorem finiteFourierPolynomial_pairing_interval
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c d : ℤ → ℂ) :
    (∫ t in (0 : ℝ)..T,
      finiteFourierPolynomial T s c (t : AddCircle T) *
        star (finiteFourierPolynomial T s d (t : AddCircle T))) =
      (T : ℂ) * ∑ n ∈ s, c n * star (d n) := by
  let h : AddCircle T → ℂ := fun θ =>
    finiteFourierPolynomial T s c θ *
      star (finiteFourierPolynomial T s d θ)
  have hI :
      (∫ t in (0 : ℝ)..T,
        finiteFourierPolynomial T s c (t : AddCircle T) *
          star (finiteFourierPolynomial T s d (t : AddCircle T))) =
        ∫ θ : AddCircle T, h θ := by
    simpa only [h, zero_add] using
      (AddCircle.intervalIntegral_preimage T 0 h)
  have hH :
      (∫ θ : AddCircle T, h θ ∂@haarAddCircle T _) =
        (T : ℂ)⁻¹ * ∫ θ : AddCircle T, h θ := by
    simpa [smul_eq_mul] using AddCircle.integral_haarAddCircle (T := T) (f := h)
  have hT : (T : ℂ) ≠ 0 := by
    exact_mod_cast (Fact.out : 0 < T).ne'
  rw [hI]
  have hp := finiteFourierPolynomial_pairing T s c d
  change (∫ θ : AddCircle T, h θ ∂@haarAddCircle T _) = _ at hp
  rw [hH] at hp
  calc
    (∫ θ : AddCircle T, h θ) =
        (T : ℂ) * ((T : ℂ)⁻¹ * ∫ θ : AddCircle T, h θ) := by
          field_simp
    _ = (T : ℂ) * ∑ n ∈ s, c n * star (d n) := by rw [hp]

/-- Finite signed mode energy on the unnormalized angle interval. A negative
Fourier frequency contributes its negative squared energy. -/
theorem finiteFourierPolynomial_signed_pairing_interval
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ t in (0 : ℝ)..T,
      finiteFourierPolynomial T s c (t : AddCircle T) *
        star (finiteFourierPolynomial T s
          (fun n => (n : ℂ) * c n) (t : AddCircle T))) =
      (T : ℂ) * ∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
  have hsum :
      (∑ n ∈ s, c n * star ((n : ℂ) * c n)) =
        ∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    calc
      _ = (∫ θ : AddCircle T,
          finiteFourierPolynomial T s c θ *
            star (finiteFourierPolynomial T s
              (fun n => (n : ℂ) * c n) θ)
          ∂@haarAddCircle T _) :=
        (finiteFourierPolynomial_pairing T s c
          (fun n => (n : ℂ) * c n)).symm
      _ = _ := finiteFourierPolynomial_signed_pairing T s c
  rw [finiteFourierPolynomial_pairing_interval, hsum]
end SpringerLean