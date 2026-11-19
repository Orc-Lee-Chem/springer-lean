import SpringerLean.Round2022EvenPowerImageComplement

namespace SpringerLean

set_option linter.style.haveILetI false

def EvenGeneratorInvariant (K : Set ℂ) (k : ℕ) : Prop :=
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
  ∀ z ∈ K, ζ*z ∈ K

theorem evenGeneratorInvariant_to_evenRotationInvariant
    (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hgen : EvenGeneratorInvariant K k) :
    EvenRotationInvariant K k := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
  have hk2 : (2*k : ℕ) ≠ 0 := by omega
  have hζ : IsPrimitiveRoot ζ (2*k) :=
    Complex.isPrimitiveRoot_exp (2*k) hk2
  have hpow (n : ℕ) (z : ℂ) (hz : z ∈ K) : ζ^n*z ∈ K := by
    induction n with
    | zero => simpa using hz
    | succ n ih =>
      have h : ζ * (ζ^n*z) ∈ K := hgen (ζ^n*z) ih
      convert h using 1; ring
  intro η z hη hz
  letI : NeZero (2*k) := ⟨hk2⟩
  obtain ⟨n, _, hn⟩ := hζ.eq_pow_of_pow_eq_one hη
  rw [← hn]
  exact hpow n z hz

theorem evenGenerator_powerImage_compl_eq
    (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hgen : EvenGeneratorInvariant K k) :
    (fun w : ℂ => w ^ k) '' Kᶜ =
      ((fun w : ℂ => w ^ k) '' K)ᶜ :=
  evenPower_image_compl_eq K k hk
    (evenGeneratorInvariant_to_evenRotationInvariant K k hk hgen)

theorem evenExteriorPowerQuotient_image_compl_of_generator
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hcov : EvenExteriorCovariant F k)
    (hgen : EvenGeneratorInvariant K k)
    (hF : F '' exteriorDisk = Kᶜ) :
    evenExteriorPowerQuotient F k '' exteriorDisk =
      ((fun w : ℂ => w ^ k) '' K)ᶜ :=
  evenExteriorPowerQuotient_image_compl F K k hk hcov
    (evenGeneratorInvariant_to_evenRotationInvariant K k hk hgen) hF

end SpringerLean

#print axioms SpringerLean.evenGeneratorInvariant_to_evenRotationInvariant
#print axioms SpringerLean.evenGenerator_powerImage_compl_eq
#print axioms SpringerLean.evenExteriorPowerQuotient_image_compl_of_generator
