import SpringerLean.Round2033EvenQuotientCoefficientBridge

open Filter
open scoped Topology

namespace SpringerLean

theorem actualTaylorCoeff_comp_const_mul_local
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0)
    (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) :
    actualTaylorCoeff (fun u : ℂ => f (c*u)) n =
      c^n * actualTaylorCoeff f n := by
  obtain ⟨r, hr, hOn⟩ := hf.exists_ball_analyticOnNhd
  let s : Set ℂ := Metric.ball 0 r
  have hs : IsOpen s := Metric.isOpen_ball
  have hdiff : UniqueDiffOn ℂ s := hs.uniqueDiffOn
  have hcont : ContDiffOn ℂ n f s := by
    intro u hu
    exact ((hOn u hu).contDiffAt.of_le le_top).contDiffWithinAt
  have hmap : Set.MapsTo (c * ·) s s := by
    intro u hu
    simpa only [s, Metric.mem_ball, dist_zero_right, norm_mul,
      hc, one_mul] using hu
  have hzero : (0:ℂ) ∈ s := by simpa [s] using hr
  have hder := iteratedDerivWithin_comp_const_smul hzero hdiff hcont c hmap
  have hcomp : AnalyticAt ℂ (fun u : ℂ => f (c*u)) 0 :=
    AnalyticAt.comp (f := fun u : ℂ => c*u) (by simpa using hf)
      (by fun_prop : AnalyticAt ℂ (fun u : ℂ => c*u) 0)
  simp only [mul_zero] at hder
  rw [iteratedDerivWithin_eq_iteratedDeriv hdiff
      (hcomp.contDiffAt.of_le le_top) hzero,
      iteratedDerivWithin_eq_iteratedDeriv hdiff
      (hf.contDiffAt.of_le le_top) hzero] at hder
  simp only [smul_eq_mul] at hder
  simp only [actualTaylorCoeff, hder]
  ring

theorem evenExteriorPhi_generator_germ_invariant
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
    (fun u : ℂ => exteriorPhi F (ζ*u)) =ᶠ[𝓝 (0:ℂ)] exteriorPhi F := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
  have hζ : IsPrimitiveRoot ζ (2*k) :=
    Complex.isPrimitiveRoot_exp (2*k) (by omega : 2*k ≠ 0)
  have hζroot : ζ^(2*k)=1 := hζ.pow_eq_one
  have hζnorm : ‖ζ‖=1 := Complex.norm_eq_one_of_pow_eq_one hζroot (by omega)
  have hζ0 : ζ ≠ 0 := by
    intro hh
    rw [hh, zero_pow (by omega : 2*k ≠ 0)] at hζroot
    norm_num at hζroot
  have hζinvroot : (ζ⁻¹)^(2*k)=1 := by rw [inv_pow, hζroot, inv_one]
  have hcov := evenExteriorCovariant_actual F K k hk hF hK hImage
  change (fun u : ℂ => exteriorPhi F (ζ*u)) =ᶠ[𝓝 (0:ℂ)] exteriorPhi F
  filter_upwards [Metric.ball_mem_nhds (0:ℂ)
    (by norm_num : (0:ℝ)<1)] with u hu
  by_cases hu0 : u=0
  · simp [hu0]
  · have hunorm : ‖u‖ < 1 := by simpa using hu
    have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have huInv : u⁻¹ ∈ exteriorDisk := by
      change 1 < ‖u⁻¹‖
      rw [norm_inv]
      exact (one_lt_inv₀ hupos).2 hunorm
    have hζu0 : ζ*u ≠ 0 := mul_ne_zero hζ0 hu0
    have hphi (t : ℂ) (ht : t ≠ 0) :
        exteriorPhi F t = t * F t⁻¹ := by
      rw [exteriorPhi, exteriorForwardGerm_punctured F ht]
      field_simp [ht]
      ring
    rw [hphi (ζ*u) hζu0, hphi u hu0, mul_inv_rev]
    have hh := hcov ζ⁻¹ u⁻¹ hζinvroot huInv
    rw [show u⁻¹*ζ⁻¹ = ζ⁻¹*u⁻¹ by ring, hh]
    field_simp [hζ0]

theorem evenExteriorPhi_low_coeff_zero
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ)
    (n : ℕ) (hn0 : 0 < n) (hn : n < 2*k) :
    actualTaylorCoeff (exteriorPhi F) n = 0 := by
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2*k : ℕ) : ℂ))
  have hζ : IsPrimitiveRoot ζ (2*k) :=
    Complex.isPrimitiveRoot_exp (2*k) (by omega : 2*k ≠ 0)
  have hζnorm : ‖ζ‖=1 :=
    Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one (by omega)
  have hEq := actualTaylorCoeff_congr
    (evenExteriorPhi_generator_germ_invariant F K k hk hF hK hImage) n
  rw [actualTaylorCoeff_comp_const_mul_local (exteriorPhi F)
    (exteriorPhi_analyticAt F hF.2.2) ζ hζnorm n] at hEq
  have hζne : ζ^n ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by omega) hn
  have hmul : (ζ^n-1)*actualTaylorCoeff (exteriorPhi F) n=0 := by
    linear_combination hEq
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hζne)

theorem powerSeries_coeff_m_pow_one_add_high
    (H : PowerSeries ℂ) (m n : ℕ) (hm : 0 < m) :
    PowerSeries.coeff m ((1 + PowerSeries.X^m * H)^n) =
      (n:ℂ) * PowerSeries.coeff 0 H := by
  let P : PowerSeries ℂ := 1 + PowerSeries.X^m * H
  have hP0 : PowerSeries.constantCoeff P = 1 := by
    dsimp [P]
    have hhigh : PowerSeries.constantCoeff (PowerSeries.X^m * H) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff,
        PowerSeries.coeff_X_pow_mul']
      simp [Nat.not_le.mpr hm]
    simp [hhigh]
  induction n with
  | zero =>
      simp [P, hm.ne']
  | succ n ih =>
      change PowerSeries.coeff m (P^(n+1)) = _
      rw [pow_succ, show P^n * P = P^n + PowerSeries.X^m * (P^n * H) by
        dsimp [P]; ring]
      have hshift : PowerSeries.coeff m
          (PowerSeries.X^m * (P^n * H)) =
          PowerSeries.coeff 0 (P^n * H) := by
        simpa only [Nat.zero_add] using
          PowerSeries.coeff_X_pow_mul (P^n * H) m 0
      rw [map_add, hshift]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff,
        map_mul, map_pow, hP0, one_pow, one_mul]
      rw [ih]
      simp only [PowerSeries.coeff_zero_eq_constantCoeff]
      push_cast
      ring

theorem powerSeries_coeff_m_pow_of_gap
    (P : PowerSeries ℂ) (m n : ℕ) (hm : 0 < m)
    (h0 : PowerSeries.coeff 0 P = 1)
    (hgap : ∀ j, 0 < j → j < m → PowerSeries.coeff j P = 0) :
    PowerSeries.coeff m (P^n) = (n:ℂ) * PowerSeries.coeff m P := by
  let H : PowerSeries ℂ := PowerSeries.mk (fun j => PowerSeries.coeff (j+m) P)
  have htrunc : (P.trunc m : PowerSeries ℂ) = 1 := by
    ext j
    by_cases hj0 : j=0
    · subst j
      simp [PowerSeries.coeff_trunc, hm, h0]
    · by_cases hjm : j<m
      · simp [PowerSeries.coeff_trunc, hjm, hgap j (Nat.pos_of_ne_zero hj0) hjm, hj0]
      · simp [PowerSeries.coeff_trunc, hjm, hj0]
  have hsplit := PowerSeries.eq_X_pow_mul_shift_add_trunc m P
  have hP : P = 1 + PowerSeries.X^m * H := by
    rw [htrunc] at hsplit
    simpa only [H, add_comm] using hsplit
  have hH0 : PowerSeries.coeff 0 H = PowerSeries.coeff m P := by
    simp [H]
  calc
    PowerSeries.coeff m (P^n) =
        PowerSeries.coeff m ((1+PowerSeries.X^m*H)^n) := by rw [hP]
    _ = (n:ℂ)*PowerSeries.coeff 0 H :=
      powerSeries_coeff_m_pow_one_add_high H m n hm
    _ = (n:ℂ)*PowerSeries.coeff m P := by rw [hH0]

/-- The actual first Laurent coefficient of the even power quotient is
the original `(2k-1)`st forward coefficient times `k`. -/
theorem evenExteriorPowerQuotient_firstCoeff_eq_k_mul_forwardCoeff
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    exteriorForwardCoeff (evenExteriorPowerQuotient F k) 1 =
      (k:ℂ) * exteriorForwardCoeff F (2*k-1) := by
  let P : PowerSeries ℂ := actualTaylorSeries (exteriorPhi F)
  have hm : 0 < 2*k := by omega
  have hP0 : PowerSeries.coeff 0 P = 1 := by
    simp [P, actualTaylorCoeff_exteriorPhi_zero]
  have hgap : ∀ j, 0 < j → j < 2*k → PowerSeries.coeff j P = 0 := by
    intro j hj0 hj
    simpa only [P, actualTaylorSeries_coeff] using
      evenExteriorPhi_low_coeff_zero F K k hk hF hK hImage j hj0 hj
  have hpower := powerSeries_coeff_m_pow_of_gap P (2*k) k hm hP0 hgap
  have hlast : PowerSeries.coeff (2*k) P =
      exteriorForwardCoeff F (2*k-1) := by
    have hidx : (2*k-1)+1=2*k := by omega
    simpa only [P, actualTaylorSeries_coeff, hidx] using
      actualTaylorCoeff_exteriorPhi_succ F hF (2*k-1)
  calc
    exteriorForwardCoeff (evenExteriorPowerQuotient F k) 1 =
        PowerSeries.coeff (2*k) (P^k) :=
      evenExteriorPowerQuotient_firstCoeff_eq_powerTaylorCoeff
        F K k hk hF hK hImage
    _ = (k:ℂ)*PowerSeries.coeff (2*k) P := hpower
    _ = (k:ℂ)*exteriorForwardCoeff F (2*k-1) := by rw [hlast]

theorem evenExteriorPowerQuotient_secondMoment_original_coeff
    (F : ℂ → ℂ) (K : Set ℂ) (k : ℕ) (hk : 0 < k)
    (hF : CenteredExteriorUnivalent F)
    (hK : EvenGeneratorInvariant K k)
    (hImage : F '' exteriorDisk = Kᶜ) :
    actualBoundaryRadialMoment (evenExteriorPowerQuotient F k) 2 ≤
      2 - (2/3:ℝ) *
        (1 - (k:ℝ)^2 * ‖exteriorForwardCoeff F (2*k-1)‖^2) := by
  have hmoment := evenExteriorPowerQuotient_actual_secondMoment
    F K k hk hF hK hImage
  rw [evenExteriorPowerQuotient_firstCoeff_eq_k_mul_forwardCoeff
      F K k hk hF hK hImage] at hmoment
  simpa only [norm_mul, Complex.norm_natCast, mul_pow] using hmoment

end SpringerLean
