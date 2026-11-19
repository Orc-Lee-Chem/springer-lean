import SpringerLean.Round1352CatalanCircleMoment

namespace SpringerLean

/-- The normalized absolute-cosine moment decreases with the exponent.
In the project's scaled moments this reads `I_(n+1)/2 ≤ I_n`. -/
theorem comparisonCircleMoment_succ_half_le (n : ℕ) :
    Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^(n+1)) 0 1 / 2 ≤
      Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 := by
  rw [comparisonCircleMoment_eq_sinMoment,
    comparisonCircleMoment_eq_sinMoment]
  unfold comparisonSinMoment
  have hmono := integral_sin_pow_succ_le n
  have hfactor : 0 ≤ (2:ℝ)^n/Real.pi := by positivity
  have hh := mul_le_mul_of_nonneg_left hmono hfactor
  change ((2:ℝ)^(n+1)/Real.pi *
    (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(n+1)))/2 ≤
    (2:ℝ)^n/Real.pi *
      (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^n)
  calc
    _ = (2:ℝ)^n/Real.pi *
      (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^(n+1)) := by
        rw [pow_succ]
        ring
    _ ≤ (2:ℝ)^n/Real.pi *
      (∫ θ in (0:ℝ)..Real.pi, Real.sin θ^n) := hh

/-- The comparison-circle moment is large enough to pay the
`39/20` platform at all requested odd orders. -/
theorem comparisonCircleMoment_odd_platform_lower
    (k : ℕ) (hk : 751 ≤ k) :
    (2:ℝ)^(2*k-1) / (2*((2*k-1:ℕ):ℝ)) ≤
      Real.circleAverage
        (fun ζ : ℂ => |2*ζ.re|^(2*k-1)) 0 1 := by
  let n : ℕ := 2*k-1
  have hn : 1501 ≤ n := by dsimp [n]; omega
  have hnR : (1501:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hkR : (751:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  let c : ℝ := normalizedCatalanOddMoment (k-1)
  have hc0 : 0 ≤ c := normalizedCatalanOddMoment_nonneg (k-1)
  have hsq := normalizedCatalanOddMoment_square_lower (k-1)
  have hcast : ((k-1:ℕ):ℝ)+1 = (k:ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    ring
  rw [hcast] at hsq
  change 1 ≤ 4*(k:ℝ)*c^2 at hsq
  have hnsq : (k:ℝ) ≤ (n:ℝ)^2 := by
    have hnk : k ≤ n := by dsimp [n]; omega
    have hnkR : (k:ℝ) ≤ n := by exact_mod_cast hnk
    nlinarith
  have hclowerSq : (1/(2*(n:ℝ)))^2 ≤ c^2 := by
    have hsmall : 4*(k:ℝ) ≤ 4*(n:ℝ)^2 := by nlinarith [hnsq]
    have hprod := mul_le_mul_of_nonneg_right hsmall (sq_nonneg c)
    have htarget : 1/(4*(n:ℝ)^2) ≤ c^2 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ)<4*(n:ℝ)^2)).2
      nlinarith [hsq, hprod]
    have hsqform : (1/(2*(n:ℝ)))^2 = 1/(4*(n:ℝ)^2) := by ring
    rw [hsqform]
    exact htarget
  have hclower : 1/(2*(n:ℝ)) ≤ c := by
    have hlow0 : (0:ℝ) ≤ 1/(2*(n:ℝ)) := by positivity
    nlinarith
  have hscaled : (2:ℝ)^n*c =
      (n:ℝ)*(catalan (k-1) : ℝ) := by
    have hI := comparisonCircleMoment_even_half_eq_scaledCatalan k (by omega)
    have hEven := comparisonCircleMoment_even_eq_normalizedCatalan (k-1)
    have hid : 2*k=2*(k-1)+2 := by omega
    rw [← hid] at hEven
    rw [hEven] at hI
    have hpow : (2:ℝ)^(2*k)/2 = (2:ℝ)^n := by
      have hnk : n+1=2*k := by dsimp [n]; omega
      rw [← hnk, pow_succ]
      ring
    change (2:ℝ)^(2*k)*c/2 =
      (((2*k-1:ℕ):ℝ))*(catalan (k-1) : ℝ) at hI
    calc
      (2:ℝ)^n*c = ((2:ℝ)^(2*k)/2)*c := by rw [hpow]
      _ = (2:ℝ)^(2*k)*c/2 := by ring
      _ = (n:ℝ)*(catalan (k-1) : ℝ) := by simpa [n] using hI
  have hmon := comparisonCircleMoment_succ_half_le n
  have hnk : n+1=2*k := by dsimp [n]; omega
  rw [hnk, comparisonCircleMoment_even_half_eq_scaledCatalan k (by omega)] at hmon
  have hpow : (2:ℝ)^n / (2*(n:ℝ)) ≤ (2:ℝ)^n*c := by
    have hpos : 0 ≤ (2:ℝ)^n := by positivity
    have h := mul_le_mul_of_nonneg_left hclower hpos
    convert h using 1 <;> ring
  change (2:ℝ)^n / (2*(n:ℝ)) ≤ _
  exact hpow.trans (hscaled.le.trans hmon)

end SpringerLean

#print axioms SpringerLean.comparisonCircleMoment_succ_half_le
#print axioms SpringerLean.comparisonCircleMoment_odd_platform_lower
