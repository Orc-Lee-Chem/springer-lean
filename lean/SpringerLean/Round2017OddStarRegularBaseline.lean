import SpringerLean.Round2016OddStarActualFarthestVariation
import Mathlib.RingTheory.RootsOfUnity.Complex

set_option maxHeartbeats 200000

namespace SpringerLean

private theorem odd_root_cos_lower_low (k j : ℕ) (hj : j ≤ k) :
    Real.cos (Real.pi - Real.pi / ((2*k+1 : ℕ) : ℝ)) ≤
      Real.cos (2*Real.pi*(j:ℝ)/((2*k+1 : ℕ) : ℝ)) := by
  have hmpos : (0 : ℝ) < ((2*k+1 : ℕ) : ℝ) := by positivity
  have hδeq : Real.pi - Real.pi / ((2*k+1 : ℕ) : ℝ) =
      2*Real.pi*(k:ℝ)/((2*k+1 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  rw [hδeq]
  have hθ : 0 ≤ 2*Real.pi*(j:ℝ)/((2*k+1 : ℕ) : ℝ) := by positivity
  have hδ : 2*Real.pi*(k:ℝ)/((2*k+1 : ℕ) : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hmpos).2
    calc
      2*Real.pi*(k:ℝ) = Real.pi*(2*(k:ℝ)) := by ring
      _ ≤ Real.pi*(2*(k:ℝ)+1) := by gcongr; norm_num
      _ = Real.pi*((2*k+1 : ℕ) : ℝ) := by push_cast; ring
  have hle : 2*Real.pi*(j:ℝ)/((2*k+1 : ℕ) : ℝ) ≤
      2*Real.pi*(k:ℝ)/((2*k+1 : ℕ) : ℝ) := by
    gcongr
  exact Real.cos_le_cos_of_nonneg_of_le_pi hθ hδ hle

private theorem odd_root_cos_lower_aux (k j : ℕ) (hj : j < 2*k+1) :
    Real.cos (Real.pi - Real.pi / ((2*k+1 : ℕ) : ℝ)) ≤
      Real.cos (2*Real.pi*(j:ℝ)/((2*k+1 : ℕ) : ℝ)) := by
  by_cases h : j ≤ k
  · exact odd_root_cos_lower_low k j h
  · have hj' : 2*k+1-j ≤ k := by omega
    have hsum : (j:ℝ) + ((2*k+1-j:ℕ):ℝ) = ((2*k+1:ℕ):ℝ) := by
      exact_mod_cast Nat.add_sub_of_le (by omega : j ≤ 2*k+1)
    have hmpos : (0 : ℝ) < ((2*k+1 : ℕ) : ℝ) := by positivity
    have hθeq : 2*Real.pi*((2*k+1-j:ℕ):ℝ)/((2*k+1 : ℕ) : ℝ) =
        2*Real.pi - 2*Real.pi*(j:ℝ)/((2*k+1 : ℕ) : ℝ) := by
      have hsub : ((2*k+1-j:ℕ):ℝ) = ((2*k+1:ℕ):ℝ) - (j:ℝ) := by
        linarith [hsum]
      rw [hsub]
      field_simp
    rw [← Real.cos_two_pi_sub (2*Real.pi*(j:ℝ)/((2*k+1 : ℕ) : ℝ)), ← hθeq]
    exact odd_root_cos_lower_low k (2*k+1-j) hj'

theorem odd_root_re_lower (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (η : ℂ) (hη : η ^ m = 1) :
    Real.cos (Real.pi - Real.pi / (m:ℝ)) ≤ η.re := by
  rcases hodd with ⟨k, rfl⟩
  have hprim : IsPrimitiveRoot
      (Complex.exp (2*Real.pi*Complex.I/((2*k+1 : ℕ):ℝ))) (2*k+1) :=
    Complex.isPrimitiveRoot_exp (2*k+1) (by omega)
  obtain ⟨j,hj,hjη⟩ := hprim.eq_pow_of_pow_eq_one hη
  rw [← hjη]
  have hre : (Complex.exp
      (2*Real.pi*Complex.I/((2*k+1 : ℕ):ℝ)) ^ j).re =
      Real.cos (2*Real.pi*(j:ℝ)/((2*k+1 : ℕ):ℝ)) := by
    rw [← Complex.exp_nat_mul]
    have hexp :
        (j:ℂ) * (2*Real.pi*Complex.I/((2*k+1 : ℕ):ℝ)) =
          ((2*Real.pi*(j:ℝ)/((2*k+1 : ℕ):ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.exp_mul_I]
    norm_cast
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      add_zero, mul_one, sub_self]
  rw [hre]
  exact odd_root_cos_lower_aux k j hj

private theorem star_cos_distance_formula (r ρ : ℝ) (η : ℂ)
    (hη : ‖η‖ = 1) :
    ‖(r:ℂ) - (ρ:ℂ)*η‖^2 = r^2 + ρ^2 - 2*r*ρ*η.re := by
  have hηsq : Complex.normSq η = 1 := by
    rw [Complex.normSq_eq_norm_sq, hη]
    norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  simp [Complex.mul_re, hηsq]
  ring

private theorem star_distance_le_opposite
    (r ρ R : ℝ) (η ζ : ℂ)
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R)
    (hη : ‖η‖ = 1) (hζ : ‖ζ‖ = 1)
    (hreal : ζ.re ≤ η.re) (hneg : ζ.re ≤ 0) :
    ‖(r:ℂ) - (ρ:ℂ)*η‖ ≤ ‖(r:ℂ) - (R:ℂ)*ζ‖ := by
  have hρ2 : ρ^2 ≤ R^2 := pow_le_pow_left₀ hρ hρR 2
  have hcross1 : -(2*r*ρ*η.re) ≤ -(2*r*ρ*ζ.re) :=
    neg_le_neg (mul_le_mul_of_nonneg_left hreal (by positivity))
  have hcross2 : -(2*r*ρ*ζ.re) ≤ -(2*r*R*ζ.re) := by
    have hh := mul_le_mul_of_nonneg_right hρR
      (show 0 ≤ -(2*r*ζ.re) by nlinarith [mul_nonpos_of_nonneg_of_nonpos hr hneg])
    nlinarith
  have hsq1 := star_cos_distance_formula r ρ η hη
  have hsq2 := star_cos_distance_formula r R ζ hζ
  have hsq : ‖(r:ℂ) - (ρ:ℂ)*η‖^2 ≤
      ‖(r:ℂ) - (R:ℂ)*ζ‖^2 := by
    rw [hsq1, hsq2]
    linarith
  nlinarith [norm_nonneg ((r:ℂ) - (ρ:ℂ)*η),
    norm_nonneg ((r:ℂ) - (R:ℂ)*ζ)]

theorem oddStarRegularRay_farthestDistance_eq
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (r : ℝ) (hr : 0 ≤ r) :
    continuumFarthestDistance (regularStarRaySet m) (r:ℂ) =
      ‖(r:ℂ) - (oddStarTipRadius m 0 : ℂ) *
        Complex.exp (((Real.pi - Real.pi / (m:ℝ):ℝ):ℂ)*Complex.I)‖ := by
  let R : ℝ := oddStarTipRadius m 0
  let ζ : ℂ := Complex.exp (((Real.pi - Real.pi / (m:ℝ):ℝ):ℂ)*Complex.I)
  have hRpos : 0 < R := oddStarTipRadius_zero_pos m
  have hRpow : R ^ m = 4 := by
    have hh := Real.rpow_inv_natCast_pow (show (0:ℝ) ≤ 4 by norm_num)
      (by omega : m ≠ 0)
    simpa [R, oddStarTipRadius] using hh
  have hζpow : ζ ^ m = 1 := oddStarOppositeTip_phase_pow_one m (by omega) hodd
  have hζnorm : ‖ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hζpow (by omega)
  have hζre : ζ.re = Real.cos (Real.pi - Real.pi / (m:ℝ)) := by
    dsimp [ζ]
    rw [Complex.exp_mul_I]
    norm_cast
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, add_zero,
      mul_one, sub_self]
  have hζneg : ζ.re ≤ 0 := by
    rw [hζre]
    exact (oddStar_opposite_tip_angle_geometry m hm 0 0 (le_refl _) (le_refl _)).2.1.le
  have hK : IsCompact (regularStarRaySet m) := by
    rw [← oddStarPerturbation_zero_omitted_eq_regularStarRays m (by omega)]
    exact oddStarPerturbation_omitted_isCompact m (by omega) 0 (by norm_num)
  have htip : (R:ℂ)*ζ ∈ regularStarRaySet m := by
    rw [← oddStarPerturbation_zero_omitted_eq_regularStarRays m (by omega)]
    exact oddStarOppositeTip_mem_omitted m hm hodd 0 (by norm_num)
  have hupper : ∀ w ∈ regularStarRaySet m,
      ‖(r:ℂ) - w‖ ≤ ‖(r:ℂ) - (R:ℂ)*ζ‖ := by
    intro w hw
    obtain ⟨ρ,hρ,hρpow,η,hηpow,rfl⟩ := hw
    have hρR : ρ ≤ R :=
      le_of_pow_le_pow_left₀ (by omega : m ≠ 0) hRpos.le (by rw [hRpow]; exact hρpow)
    have hηnorm : ‖η‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one hηpow (by omega)
    have hreal : ζ.re ≤ η.re := by
      rw [hζre]
      exact odd_root_re_lower m hm hodd η hηpow
    exact star_distance_le_opposite r ρ R η ζ hr hρ hρR hηnorm hζnorm hreal hζneg
  change sSup ((fun w : ℂ => ‖(r:ℂ)-w‖) '' regularStarRaySet m) = _
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, ⟨_, htip, rfl⟩⟩
    rintro y ⟨w, hw, rfl⟩
    exact hupper w hw
  · exact le_csSup (hK.image (by fun_prop : Continuous (fun w : ℂ => ‖(r:ℂ)-w‖))).bddAbove
      ⟨_, htip, rfl⟩

theorem oddStarActualBoundaryProbability_baseline_farthestLog
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    (∫ z : ℂ,
      Real.log (continuumFarthestDistance
        (oddStarPerturbationOmitted m 0) z)
      ∂oddStarActualBoundaryProbability m 0) =
    (2*Real.pi)⁻¹ *
      (∫ θ in (0:ℝ)..2*Real.pi,
        oddStarOppositeTipLogDistance m θ 0) := by
  obtain ⟨U,hU,htransfer⟩ :=
    oddStarActualBoundaryProbability_farthestLog_angular_transfer m hm
  have hzero : (0:ℝ) ∈ U := mem_of_mem_nhds hU
  rw [htransfer 0 hzero]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have hr : 0 ≤ oddStarBoundaryRadius m θ := by
    unfold oddStarBoundaryRadius
    apply Real.rpow_nonneg
    nlinarith [Real.neg_one_le_cos θ]
  have hZ : oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0 =
      (oddStarBoundaryRadius m θ : ℂ) := by
    simp [oddStarMovingBoundaryPoint, oddStarBoundaryFactor]
  change Real.log (continuumFarthestDistance
    (oddStarPerturbationOmitted m 0)
    (oddStarMovingBoundaryPoint m (oddStarBoundaryRadius m θ) θ 0)) =
      oddStarOppositeTipLogDistance m θ 0
  rw [hZ, oddStarPerturbation_zero_omitted_eq_regularStarRays m (by omega),
    oddStarRegularRay_farthestDistance_eq m hm hodd _ hr]
  simp only [oddStarOppositeTipLogDistance, hZ]

theorem oddStarActualBoundaryProbability_exists_strict_farthestLog_over_regular
    (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m) :
    ∃ t : ℝ, 0 < t ∧ |t| < 1 ∧
      (∫ z : ℂ,
        Real.log (continuumFarthestDistance
          (oddStarPerturbationOmitted m 0) z)
        ∂oddStarActualBoundaryProbability m 0) <
      (∫ z : ℂ,
        Real.log (continuumFarthestDistance
          (oddStarPerturbationOmitted m t) z)
        ∂oddStarActualBoundaryProbability m t) := by
  obtain ⟨t, htpos, ht1, hlt⟩ :=
    oddStarActualBoundaryProbability_exists_strict_farthestLog m hm hodd
  refine ⟨t, htpos, ht1, ?_⟩
  rw [oddStarActualBoundaryProbability_baseline_farthestLog m hm hodd]
  exact hlt

end SpringerLean

#print axioms SpringerLean.odd_root_re_lower
#print axioms SpringerLean.oddStarRegularRay_farthestDistance_eq
#print axioms SpringerLean.oddStarActualBoundaryProbability_baseline_farthestLog
#print axioms SpringerLean.oddStarActualBoundaryProbability_exists_strict_farthestLog_over_regular
