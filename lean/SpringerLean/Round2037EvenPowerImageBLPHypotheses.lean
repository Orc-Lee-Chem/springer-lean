import SpringerLean.Round2036EvenStarPotentialReduction

namespace SpringerLean

theorem even_generator_pow_neg_one
    (k : ℕ) (hk : 0 < k) :
    (Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ)))^k = -1 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
  have hζ : IsPrimitiveRoot ζ (2*k) :=
    Complex.isPrimitiveRoot_exp (2*k) (by omega : 2*k ≠ 0)
  have hsq : (ζ^k)^2 = 1 := by
    rw [← pow_mul, show k*2=2*k by omega, hζ.pow_eq_one]
  have hne : ζ^k ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  exact (sq_eq_one_iff.mp hsq).resolve_left hne

theorem evenPowerImage_compact_connected_zero_symmetric
    (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hcompact : IsCompact K) (hconnected : IsConnected K)
    (hzero : (0:ℂ) ∈ K) (hgen : EvenGeneratorInvariant K k) :
    let E : Set ℂ := (fun w : ℂ => w^k) '' K
    IsCompact E ∧ IsConnected E ∧ (0:ℂ) ∈ E ∧
      (∀ w ∈ E, -w ∈ E) := by
  let E : Set ℂ := (fun w : ℂ => w^k) '' K
  change IsCompact E ∧ IsConnected E ∧ (0:ℂ) ∈ E ∧
    (∀ w ∈ E, -w ∈ E)
  have hcont : Continuous (fun w : ℂ => w^k) := by fun_prop
  refine ⟨hcompact.image hcont, hconnected.image _ hcont.continuousOn,
    ⟨0, hzero, by simp [ne_of_gt hk]⟩, ?_⟩
  intro w hw
  obtain ⟨z, hz, rfl⟩ := hw
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
  have hζk : ζ^k=-1 := even_generator_pow_neg_one k hk
  have hζz : ζ*z ∈ K := by
    simpa only [ζ] using hgen z hz
  refine ⟨ζ*z, hζz, ?_⟩
  change (ζ*z)^k=-(z^k)
  rw [mul_pow, hζk, neg_one_mul]

end SpringerLean
