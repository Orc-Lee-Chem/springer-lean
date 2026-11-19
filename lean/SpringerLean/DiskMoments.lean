import SpringerLean.DiskPolar
import SpringerLean.CircleEnergy

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace SpringerLean

private instance : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

private theorem fourier_one_pow (j : ℕ) (θ : AddCircle (2 * Real.pi)) :
    (fourier (1 : ℤ) θ) ^ j = fourier (j : ℤ) θ := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, ih, ← fourier_add]
      congr 1

/-- Angular orthogonality on the exact interval used by the polar chart. -/
theorem unitDisk_fourier_pair_interval (p q : ℕ) :
    (∫ θ in -Real.pi..Real.pi,
      fourier (p : ℤ) (θ : AddCircle (2 * Real.pi)) *
        star (fourier (q : ℤ) (θ : AddCircle (2 * Real.pi)))) =
      if p = q then (2 * Real.pi : ℂ) else 0 := by
  let h : AddCircle (2 * Real.pi) → ℂ := fun θ =>
    fourier (p : ℤ) θ * star (fourier (q : ℤ) θ)
  have hI : (∫ θ in -Real.pi..Real.pi,
      fourier (p : ℤ) (θ : AddCircle (2 * Real.pi)) *
        star (fourier (q : ℤ) (θ : AddCircle (2 * Real.pi)))) =
        ∫ θ : AddCircle (2 * Real.pi), h θ := by
    simpa [h, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      (AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi) h)
  have hH : (∫ θ : AddCircle (2 * Real.pi), h θ
        ∂@haarAddCircle (2 * Real.pi) _) =
      (2 * Real.pi)⁻¹ • ∫ θ : AddCircle (2 * Real.pi), h θ := by
    exact AddCircle.integral_haarAddCircle
  have hO := fourier_pair_integral (2 * Real.pi) (p : ℤ) (q : ℤ)
  change (∫ θ : AddCircle (2 * Real.pi), h θ
      ∂@haarAddCircle (2 * Real.pi) _) =
    (if (p : ℤ) = (q : ℤ) then (1 : ℂ) else 0) at hO
  rw [hH] at hO
  have hO' : (2 * Real.pi : ℂ)⁻¹ *
      (∫ θ : AddCircle (2 * Real.pi), h θ) =
        (if (p : ℤ) = (q : ℤ) then (1 : ℂ) else 0) := by
    simpa [smul_eq_mul] using hO
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi))
  rw [hI]
  by_cases hpq : p = q
  · subst q
    simp only [ite_true] at hO' ⊢
    calc
      (∫ θ : AddCircle (2 * Real.pi), h θ) =
          (2 * Real.pi : ℂ) *
            ((2 * Real.pi : ℂ)⁻¹ * ∫ θ : AddCircle (2 * Real.pi), h θ) := by
              field_simp
      _ = (2 * Real.pi : ℂ) := by rw [hO']; ring
  · have hpq' : (p : ℤ) ≠ (q : ℤ) := by exact_mod_cast hpq
    simp only [hpq, hpq', ite_false] at hO' ⊢
    calc
      (∫ θ : AddCircle (2 * Real.pi), h θ) =
          (2 * Real.pi : ℂ) *
            ((2 * Real.pi : ℂ)⁻¹ * ∫ θ : AddCircle (2 * Real.pi), h θ) := by
              field_simp
      _ = 0 := by rw [hO']; ring

private theorem polar_monomial_eq_fourier
    (ρ θ : ℝ) (p q : ℕ) :
    (ρ : ℂ) * (Complex.polarCoord.symm (ρ, θ) : ℂ) ^ p *
        conj (Complex.polarCoord.symm (ρ, θ) : ℂ) ^ q =
      (ρ : ℂ) ^ (p + q + 1) *
        (fourier (p : ℤ) (θ : AddCircle (2 * Real.pi)) *
          star (fourier (q : ℤ) (θ : AddCircle (2 * Real.pi)))) := by
  have hpolar : (Complex.polarCoord.symm (ρ, θ) : ℂ) =
      (ρ : ℂ) * fourier (1 : ℤ) (θ : AddCircle (2 * Real.pi)) := by
    rw [← exteriorCirclePoint_eq_polarCoord_symm]
    rfl
  rw [hpolar, map_mul]
  simp only [mul_pow, Complex.conj_ofReal]
  rw [fourier_one_pow p, ← map_pow, fourier_one_pow q]
  simp only [Complex.star_def]
  ring

/-- The angular integral of a polar disk monomial is its diagonal mode. -/
theorem unitDisk_polar_monomial_angular (ρ : ℝ) (p q : ℕ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      (ρ : ℂ) * (Complex.polarCoord.symm (ρ, θ) : ℂ) ^ p *
        conj (Complex.polarCoord.symm (ρ, θ) : ℂ) ^ q ∂volume) =
      (ρ : ℂ) ^ (p + q + 1) *
        (if p = q then (2 * Real.pi : ℂ) else 0) := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hπ]
  simp_rw [polar_monomial_eq_fourier]
  rw [intervalIntegral.integral_const_mul, unitDisk_fourier_pair_interval]

private theorem unitDisk_radial_complex_pow (m : ℕ) :
    (∫ ρ in Set.Ioo (0 : ℝ) 1, (ρ : ℂ) ^ m ∂volume) =
      (1 : ℂ) / (m + 1 : ℂ) := by
  have hreal : (∫ ρ in Set.Ioo (0 : ℝ) 1, ρ ^ m ∂volume) =
      (1 : ℝ) / (m + 1 : ℝ) := by
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
    norm_num
  calc
    (∫ ρ in Set.Ioo (0 : ℝ) 1, (ρ : ℂ) ^ m ∂volume) =
        (∫ ρ in Set.Ioo (0 : ℝ) 1, ((ρ ^ m : ℝ) : ℂ) ∂volume) := by
          congr 1
          funext ρ
          norm_cast
    _ = ((∫ ρ in Set.Ioo (0 : ℝ) 1, ρ ^ m ∂volume : ℝ) : ℂ) := by
          exact integral_complex_ofReal
    _ = (1 : ℂ) / (m + 1 : ℂ) := by
          rw [hreal]
          push_cast
          ring

/-- The normalized disk monomial moment, including the unit-mass case
`p=q=0`. -/
theorem unitDisk_monomial_integral (p q : ℕ) :
    (Real.pi : ℂ)⁻¹ *
      (∫ z in Metric.ball (0 : ℂ) 1,
        z ^ p * conj z ^ q ∂volume) =
      if p = q then (p + 1 : ℂ)⁻¹ else 0 := by
  have hf : Continuous (fun z : ℂ => z ^ p * conj z ^ q) := by fun_prop
  rw [unitDisk_integral_polar _ hf]
  simp_rw [← mul_assoc, unitDisk_polar_monomial_angular]
  by_cases hpq : p = q
  · subst q
    simp only [ite_true]
    rw [integral_mul_const, unitDisk_radial_complex_pow (p + p + 1)]
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hp : (p + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : p + 1 ≠ 0)
    push_cast
    have hden : (p : ℂ) + (p : ℂ) + 1 + 1 =
        2 * ((p : ℂ) + 1) := by ring
    rw [hden]
    field_simp [hπ, hp]
  · simp only [hpq, ite_false, mul_zero, integral_zero, mul_zero]


end SpringerLean
