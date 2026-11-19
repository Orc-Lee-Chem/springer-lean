import SpringerLean.Round2043EvenStarSlitGeometry

namespace SpringerLean

theorem slitMap_unit_rotate (u z : ℂ) (hu : u ≠ 0) (hz : z ≠ 0) :
    slitMap (u^2) (u*z) = u * slitMap 1 z := by
  simp [slitMap, div_eq_mul_inv]
  field_simp [hu, hz]

theorem slitMap_rotated_image_iff
    (u w : ℂ) (hu : ‖u‖ = 1) :
    w ∈ slitMap (u^2) '' exteriorDisk ↔
      w/u ∈ slitMap 1 '' exteriorDisk := by
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  constructor
  · rintro ⟨x,hx,rfl⟩
    let z := x/u
    have hx0 := exterior_ne_zero hx
    have hz0 : z ≠ 0 := div_ne_zero hx0 hu0
    have hz : z ∈ exteriorDisk := by
      change 1 < ‖z‖
      simp [z, hu]
      exact hx
    refine ⟨z,hz,?_⟩
    have hux : u*z=x := by
      dsimp [z]
      field_simp [hu0]
    have hrot := slitMap_unit_rotate u z hu0 hz0
    rw [hux] at hrot
    rw [hrot]
    field_simp [hu0]
  · rintro ⟨z,hz,hzmap⟩
    have hz0 := exterior_ne_zero hz
    have hux : u*z ∈ exteriorDisk := by
      change 1 < ‖u*z‖
      rw [norm_mul,hu,one_mul]
      exact hz
    refine ⟨u*z,hux,?_⟩
    rw [slitMap_unit_rotate u z hu0 hz0, hzmap]
    field_simp [hu0]

theorem even_slit_power_preimage_similar_regularStar
    (k : ℕ) (hk : 0 < k) (a : ℂ) (ha : ‖a‖ = 1) :
    ∃ v : ℂ, ‖v‖ = 1 ∧
      {z : ℂ | z^k ∈ (slitMap a '' exteriorDisk)ᶜ} =
        (fun z : ℂ => v*z) '' regularStarPowerSet (2*k) := by
  obtain ⟨v,hva⟩ := IsAlgClosed.exists_pow_nat_eq a (by omega : 0 < 2*k)
  have hvnormpow : ‖v‖^(2*k) = 1 := by
    rw [←norm_pow, hva, ha]
  have hvnorm : ‖v‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg v) (by omega : 2*k ≠ 0)).mp hvnormpow
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hvnorm
  let u := v^k
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_pow,hvnorm,one_pow]
  have hua : u^2 = a := by
    dsimp [u]
    rw [←pow_mul, show k*2=2*k by omega, hva]
  refine ⟨v,hvnorm,?_⟩
  ext z
  have hmem : z^k ∈ (slitMap a '' exteriorDisk)ᶜ ↔
      z/v ∈ regularStarPowerSet (2*k) := by
    change z^k ∉ slitMap a '' exteriorDisk ↔
      z/v ∈ regularStarPowerSet (2*k)
    rw [←hua, slitMap_rotated_image_iff u (z^k) hu]
    have hp : z^k/u = (z/v)^k := by
      dsimp [u]
      rw [div_pow]
    rw [hp]
    change (z/v)^k ∈ (slitMap 1 '' exteriorDisk)ᶜ ↔
      z/v ∈ regularStarPowerSet (2*k)
    exact Set.ext_iff.mp (even_slit_power_preimage_eq_regularStarPowerSet k) _
  change z^k ∈ (slitMap a '' exteriorDisk)ᶜ ↔
    z ∈ (fun z : ℂ => v*z) '' regularStarPowerSet (2*k)
  rw [hmem]
  constructor
  · intro hz
    refine ⟨z/v,hz,?_⟩
    field_simp [hv0]
  · rintro ⟨t,ht,rfl⟩
    have hdiv : v*t/v=t := by field_simp [hv0]
    simpa [hdiv] using ht

theorem evenPowerQuotient_secondMoment_eq_two_regularStar_similarity
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (hEq : actualBoundaryRadialMoment
      (evenExteriorPowerQuotient F k) 2 = 2) :
    ∃ v : ℂ, ‖v‖ = 1 ∧
      K = (fun z : ℂ => v*z) '' regularStarPowerSet (2*k) := by
  obtain ⟨a,ha,hKslit⟩ :=
    evenPowerQuotient_secondMoment_eq_two_omitted_preimage_slit
      F K k hk hF hK hImage hEq
  obtain ⟨v,hv,hstar⟩ := even_slit_power_preimage_similar_regularStar k hk a ha
  exact ⟨v,hv,hKslit.trans hstar⟩

theorem evenPowerQuotient_forwardCoeff_full_regularStar_similarity
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (hFull : (k:ℝ)^2 * ‖exteriorForwardCoeff F (2*k-1)‖^2 = 1) :
    ∃ v : ℂ, ‖v‖ = 1 ∧
      K = (fun z : ℂ => v*z) '' regularStarPowerSet (2*k) := by
  obtain ⟨a,ha,hKslit⟩ :=
    evenPowerQuotient_forwardCoeff_full_omitted_preimage_slit
      F K k hk hF hK hImage hFull
  obtain ⟨v,hv,hstar⟩ := even_slit_power_preimage_similar_regularStar k hk a ha
  exact ⟨v,hv,hKslit.trans hstar⟩

end SpringerLean
