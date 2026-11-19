import SpringerLean.CircleEnergy

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace SpringerLean

noncomputable def finiteFourierFamily {ι : Type*} (T : ℝ)
    (s : Finset ι) (frequency : ι → ℤ) (c : ι → ℂ)
    (θ : AddCircle T) : ℂ :=
  ∑ i ∈ s, c i * fourier (frequency i) θ

/-- Finite Parseval for any family of distinct integer frequencies. -/
theorem finiteFourierFamily_energy {ι : Type*}
    (T : ℝ) [Fact (0 < T)] (s : Finset ι)
    (frequency : ι → ℤ) (c : ι → ℂ)
    (hinj : Function.Injective frequency) :
    (∫ θ : AddCircle T,
      ‖finiteFourierFamily T s frequency c θ‖ ^ 2
      ∂(@haarAddCircle T _)) =
      ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  have hpoint (θ : AddCircle T) :
      finiteFourierFamily T s frequency c θ *
          star (finiteFourierFamily T s frequency c θ) =
        ∑ i ∈ s, ∑ j ∈ s,
          (c i * star (c j)) *
            (fourier (frequency i) θ *
              star (fourier (frequency j) θ)) := by
    unfold finiteFourierFamily
    simp_rw [star_sum, star_mul]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    congr 1
    ext i
    congr 1
    ext j
    ring
  have hint (i j : ι) :
      Integrable (fun θ : AddCircle T =>
        (c i * star (c j)) *
          (fourier (frequency i) θ *
            star (fourier (frequency j) θ)))
        (@haarAddCircle T _) := by
    have hcont : Continuous (fun θ : AddCircle T =>
        (c i * star (c j)) *
          (fourier (frequency i) θ *
            star (fourier (frequency j) θ))) := by fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcomplex :
      (∫ θ : AddCircle T,
        finiteFourierFamily T s frequency c θ *
          star (finiteFourierFamily T s frequency c θ)
        ∂(@haarAddCircle T _)) =
        ∑ i ∈ s, c i * star (c i) := by
    calc
      _ = ∫ θ : AddCircle T,
          ∑ i ∈ s, ∑ j ∈ s,
            (c i * star (c j)) *
              (fourier (frequency i) θ *
                star (fourier (frequency j) θ))
          ∂(@haarAddCircle T _) := by simp only [hpoint]
      _ = ∑ i ∈ s, ∑ j ∈ s,
          (c i * star (c j)) *
            (if frequency i = frequency j then 1 else 0) := by
        rw [integral_finsetSum]
        · congr 1
          ext i
          rw [integral_finsetSum]
          · congr 1
            ext j
            rw [integral_const_mul, fourier_pair_integral]
          · intro j hj
            exact hint i j
        · intro i hi
          convert integrable_finsetSum' s (fun j hj => hint i j) using 1
          funext θ
          simp only [Finset.sum_apply]
      _ = ∑ i ∈ s, c i * star (c i) := by
        have heq (i j : ι) : (frequency i = frequency j) = (i = j) :=
          propext ⟨fun h => hinj h, fun h => congrArg frequency h⟩
        simp_rw [heq]
        simp
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  calc
    (∫ θ : AddCircle T,
      ((‖finiteFourierFamily T s frequency c θ‖ ^ 2 : ℝ) : ℂ)
      ∂(@haarAddCircle T _)) =
      ∫ θ : AddCircle T,
        finiteFourierFamily T s frequency c θ *
          star (finiteFourierFamily T s frequency c θ)
      ∂(@haarAddCircle T _) := by
        congr 1
        funext θ
        change ((‖finiteFourierFamily T s frequency c θ‖ ^ 2 : ℝ) : ℂ) =
          finiteFourierFamily T s frequency c θ *
            conj (finiteFourierFamily T s frequency c θ)
        rw [Complex.mul_conj']
        norm_cast
    _ = ∑ i ∈ s, c i * star (c i) := hcomplex
    _ = ((∑ i ∈ s, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      congr 1
      ext i
      change c i * conj (c i) = (‖c i‖ : ℂ) ^ 2
      rw [Complex.mul_conj']

end SpringerLean
