import SpringerLean.Round2014OddStarFarthestIntegral

namespace SpringerLean
open MeasureTheory

theorem oddStarComplexPrincipalRoot_measurable (m : ℕ) :
    Measurable (fun z : ℂ => z ^ ((m : ℂ)⁻¹)) := by
  fun_prop

theorem oddStarFarthestDistance_rotation
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (η z : ℂ) (hη : η ^ m = 1) :
    continuumFarthestDistance (oddStarPerturbationOmitted m t) (η * z) =
      continuumFarthestDistance (oddStarPerturbationOmitted m t) z := by
  let K := oddStarPerturbationOmitted m t
  have hK : IsCompact K := oddStarPerturbation_omitted_isCompact m hm t ht
  have hne : K.Nonempty := ⟨0, (oddStarPerturbation_omitted_tips m hm t ht).1⟩
  have hηnorm : ‖η‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hη (by omega : m ≠ 0)
  have hmono (ξ y : ℂ) (hξ : ξ ^ m = 1) (hξnorm : ‖ξ‖ = 1) :
      continuumFarthestDistance K y ≤
        continuumFarthestDistance K (ξ * y) := by
    obtain ⟨w, hw, hd⟩ :=
      continuumFarthestDistance_eq_distance_at_max K hK hne y
    have hξw : ξ * w ∈ K :=
      (oddStarPerturbation_omitted_rotation_iff m hm t ht ξ w hξ).2 hw
    calc
      continuumFarthestDistance K y = ‖y - w‖ := hd
      _ = ‖ξ * y - ξ * w‖ := by rw [← mul_sub, norm_mul, hξnorm, one_mul]
      _ ≤ continuumFarthestDistance K (ξ * y) :=
        continuumFarthestDistance_ge_distance K hK _ _ hξw
  have hη0 : η ≠ 0 := by
    intro heq
    rw [heq, zero_pow (by omega : m ≠ 0)] at hη
    norm_num at hη
  have hηinv : (η⁻¹) ^ m = 1 := by rw [inv_pow, hη, inv_one]
  have hηinvnorm : ‖η⁻¹‖ = 1 := by rw [norm_inv, hηnorm, inv_one]
  apply le_antisymm
  · have h := hmono η⁻¹ (η * z) hηinv hηinvnorm
    simpa [hη0, mul_assoc] using h
  · exact hmono η z hη hηnorm

theorem oddStarFarthestDistance_eq_of_pow_eq
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (z w : ℂ) (hpow : z ^ m = w ^ m) :
    continuumFarthestDistance (oddStarPerturbationOmitted m t) z =
      continuumFarthestDistance (oddStarPerturbationOmitted m t) w := by
  by_cases hw : w = 0
  · subst w
    have hzpow : z ^ m = 0 := by
      simpa [zero_pow (by omega : m ≠ 0)] using hpow
    have hz : z = 0 := eq_zero_of_pow_eq_zero hzpow
    subst z
    rfl
  · let η : ℂ := z / w
    have hη : η ^ m = 1 := by
      dsimp [η]
      rw [div_pow, hpow, div_self (pow_ne_zero m hw)]
    have hz : η * w = z := by
      dsimp [η]
      field_simp
    rw [← hz]
    exact oddStarFarthestDistance_rotation m hm t ht η w hη

theorem oddStarFarthestDistance_factors_through_power
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1)
    (z : ℂ) :
    continuumFarthestDistance (oddStarPerturbationOmitted m t) z =
      continuumFarthestDistance (oddStarPerturbationOmitted m t)
        ((z ^ m) ^ ((m : ℂ)⁻¹)) := by
  apply oddStarFarthestDistance_eq_of_pow_eq m hm t ht
  exact (Complex.cpow_nat_inv_pow (z ^ m) (by omega : m ≠ 0)).symm

theorem oddStarFarthestLog_principalRoot_measurable
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    Measurable (fun v : ℂ =>
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t) (v ^ ((m : ℂ)⁻¹)))) := by
  let K := oddStarPerturbationOmitted m t
  have hK : IsCompact K := oddStarPerturbation_omitted_isCompact m hm t ht
  have hne : K.Nonempty := ⟨0, (oddStarPerturbation_omitted_tips m hm t ht).1⟩
  have hroot := oddStarComplexPrincipalRoot_measurable m
  have hd := (continuumFarthestDistance_continuous K hK hne).measurable
  exact Real.measurable_log.comp (hd.comp hroot)

theorem oddStarActualBoundaryProbability_farthestLog_seed_transfer
    (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (ht : |t| < 1) :
    (∫ z : ℂ,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t) z)
      ∂oddStarActualBoundaryProbability m t) =
    (∫ v : ℂ,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t) (v ^ ((m : ℂ)⁻¹)))
      ∂oddStarSeedBoundaryProbability t) := by
  let ν := oddStarActualBoundaryProbability m t
  let P : ℂ → ℂ := fun z => z ^ m
  let ψ : ℂ → ℝ := fun v =>
    Real.log (continuumFarthestDistance
      (oddStarPerturbationOmitted m t) (v ^ ((m : ℂ)⁻¹)))
  have hP : AEMeasurable P ν := by fun_prop
  have hψ : AEStronglyMeasurable ψ (ν.map P) :=
    (oddStarFarthestLog_principalRoot_measurable m hm t ht).aestronglyMeasurable
  calc
    (∫ z : ℂ,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m t) z) ∂ν) =
        ∫ z : ℂ, ψ (P z) ∂ν := by
          apply integral_congr_ae
          filter_upwards with z
          exact congrArg Real.log
            (oddStarFarthestDistance_factors_through_power m hm t ht z)
    _ = ∫ v : ℂ, ψ v ∂(ν.map P) := (integral_map hP hψ).symm
    _ = ∫ v : ℂ, ψ v ∂oddStarSeedBoundaryProbability t := by
      rw [oddStarPerturbation_actual_boundary_probability_map_pow m hm t ht]

end SpringerLean
