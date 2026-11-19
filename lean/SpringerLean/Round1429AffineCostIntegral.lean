import SpringerLean.Round1428AffineActiveProfile
import SpringerLean.Round1380EvenCircleIntegral
import SpringerLean.Round1374HalfCosMoments

open MeasureTheory

namespace SpringerLean
set_option maxHeartbeats 250000

theorem refinedAffine_sqrt_inv_gamma
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    1/Real.sqrt (refinedAffineGamma W) =
      Real.sqrt (refinedAffineU W/refinedAffineV W) := by
  have hu : 0 < refinedAffineU W := by
    dsimp [refinedAffineU]
    positivity
  have hv : 0 < refinedAffineV W := by
    dsimp [refinedAffineV]
    nlinarith
  have heq : (refinedAffineGamma W)⁻¹ =
      refinedAffineU W/refinedAffineV W := by
    unfold refinedAffineGamma
    field_simp [ne_of_gt hu,ne_of_gt hv]
  calc
    1/Real.sqrt (refinedAffineGamma W) =
        (Real.sqrt (refinedAffineGamma W))⁻¹ := by ring
    _ = Real.sqrt ((refinedAffineGamma W)⁻¹) :=
      (Real.sqrt_inv _).symm
    _ = _ := by rw [heq]

theorem refinedAffine_angle_deriv_bound
    {W φ : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hφ0 : 0 < φ) (hφ : φ < refinedAffineBeta W) :
    deriv (refinedAffineAngle (refinedAffineGamma W)) φ ≤
      (1+(71/5000:ℝ)*W)*
        Real.sqrt (refinedAffineU W/refinedAffineV W) := by
  obtain ⟨_,_,hβ0,hβhalf,_,hβdef⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  obtain ⟨_,hs⟩ := refinedAffine_active_threshold_range hW0 hW
  have hγ := refinedAffine_gamma_pos_le_one hW0
    (hW.trans (by norm_num))
  change 0 < refinedAffineGamma W ∧ refinedAffineGamma W ≤ 1 at hγ
  have hβπ : refinedAffineBeta W ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    hφ0.le hβπ hφ.le
  have hshort : 2-2*Real.cos φ <
      refinedAffineGamma W*(51/500:ℝ) := by
    have hβsmall : 2-2*Real.cos (refinedAffineBeta W) <
        refinedAffineGamma W*(51/500:ℝ) := by
      rw [hβdef]
      exact mul_lt_mul_of_pos_left hs hγ.1
    linarith
  let θ : ℝ := refinedAffineAngle (refinedAffineGamma W) φ
  let s : ℝ := 2-2*Real.cos θ
  have hθdef := refinedAffine_angle_deficit hγ.1 hφ0.le
    (hφ.le.trans hβhalf) hshort.le
  change refinedAffineGamma W*s=2-2*Real.cos φ at hθdef
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith [Real.cos_le_one θ]
  have hsupper : s ≤ 51/500 := by
    have hmul : refinedAffineGamma W*s <
        refinedAffineGamma W*(51/500:ℝ) := by
      rw [hθdef]
      exact hshort
    exact (lt_of_mul_lt_mul_left hmul hγ.1.le).le
  have hgap := refinedAffine_one_sub_gamma_le hW0 hW
  change 1-refinedAffineGamma W ≤ (107107/100000:ℝ)*W at hgap
  have hroot := refinedAffine_jacobian_sqrt_le hW0 hW hs0
    hsupper hγ.1.le hγ.2 hgap
  have hderiv := refinedAffine_angle_deriv_formula hγ.1 hγ.2
    hφ0 (hφ.trans_le hβhalf) hshort
  change deriv (refinedAffineAngle (refinedAffineGamma W)) φ =
      Real.sqrt ((4-refinedAffineGamma W*s)/(4-s)) /
        Real.sqrt (refinedAffineGamma W) at hderiv
  rw [hderiv]
  have hmul := mul_le_mul_of_nonneg_right hroot
    (show 0 ≤ 1/Real.sqrt (refinedAffineGamma W) by positivity)
  rw [refinedAffine_sqrt_inv_gamma hW0 hW] at hmul
  calc
    Real.sqrt ((4-refinedAffineGamma W*s)/(4-s)) /
        Real.sqrt (refinedAffineGamma W) =
      Real.sqrt ((4-refinedAffineGamma W*s)/(4-s)) *
        (1/Real.sqrt (refinedAffineGamma W)) := by ring
    _ = Real.sqrt ((4-refinedAffineGamma W*s)/(4-s)) *
        Real.sqrt (refinedAffineU W/refinedAffineV W) := by
      rw [refinedAffine_sqrt_inv_gamma hW0 hW]
    _ ≤ _ := hmul

theorem refinedAffine_angle_deriv_continuousOn
    {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500) :
    ContinuousOn (deriv (refinedAffineAngle (refinedAffineGamma W)))
      (Set.Icc 0 (refinedAffineBeta W)) := by
  intro φ hφ
  obtain ⟨_,_,hβ0,hβhalf,_,hβdef⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  obtain ⟨_,hs⟩ := refinedAffine_active_threshold_range hW0 hW
  have hγ := refinedAffine_gamma_pos_le_one hW0
    (hW.trans (by norm_num))
  change 0 < refinedAffineGamma W ∧ refinedAffineGamma W ≤ 1 at hγ
  have hβπ : refinedAffineBeta W ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    hφ.1 hβπ hφ.2
  have hshort : 2-2*Real.cos φ ≤
      refinedAffineGamma W*(51/500:ℝ) := by
    have hβsmall : 2-2*Real.cos (refinedAffineBeta W) <
        refinedAffineGamma W*(51/500:ℝ) := by
      rw [hβdef]
      exact mul_lt_mul_of_pos_left hs hγ.1
    linarith
  obtain ⟨hq0,hq1⟩ := refinedAffine_angle_argument_range
    hγ.1 hφ.1 (hφ.2.trans hβhalf) hshort
  have harg : ContDiffAt ℝ 1
      (fun w : ℝ => Real.sin (w/2)/Real.sqrt (refinedAffineGamma W)) φ := by
    fun_prop (disch := positivity)
  have hangle : ContDiffAt ℝ 1
      (refinedAffineAngle (refinedAffineGamma W)) φ := by
    unfold refinedAffineAngle
    exact contDiffAt_const.mul ((Real.contDiffAt_arcsin
      (by linarith [hq0]) (by linarith [hq1])).comp φ harg)
  exact (hangle.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

/-- The active piece of the affine model costs at most the positive
half-circle cosine moment times the scalar amplification factor. -/
theorem refinedAffine_active_integral_le
    (n : ℕ) {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hWsq : (n:ℝ)*W^2 ≤ 3/500) :
    (∫ θ in (0:ℝ)..refinedAffineAlpha W,
      refinedAffineRadius W (2*Real.cos θ)^n) ≤
      (2:ℝ)^n*halfCosMoment n*
        (1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2) := by
  let γ := refinedAffineGamma W
  let b := refinedAffineBeta W
  let amp : ℝ := 1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2
  let g : ℝ → ℝ := fun φ => (2*Real.cos φ)^n*amp
  let f : ℝ → ℝ := fun θ => refinedAffineRadius W (2*Real.cos θ)^n
  obtain ⟨_,_,hb0,hbhalf,_,hbdef⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  obtain ⟨_,hs⟩ := refinedAffine_active_threshold_range hW0 hW
  have hγ := refinedAffine_gamma_pos_le_one hW0
    (hW.trans (by norm_num))
  change 0 < γ ∧ γ ≤ 1 at hγ
  have hshort : 2-2*Real.cos b < γ*(51/500:ℝ) := by
    rw [hbdef]
    exact mul_lt_mul_of_pos_left hs hγ.1
  have hsub := refinedAffine_angle_integral_substitution
    hγ.1 hγ.2 hb0 hbhalf hshort f
  rw [refinedAffine_angle_beta_eq_alpha hW0 hW] at hsub
  have hpoint : ∀ φ ∈ Set.Ioo 0 b,
      f (refinedAffineAngle γ φ) *
        deriv (refinedAffineAngle γ) φ ≤ g φ := by
    intro φ hφ
    have hprofile := refinedAffine_profile_at_angle hW0 hW
      hφ.1.le hφ.2.le
    have hderiv := refinedAffine_angle_deriv_bound hW0 hW hφ.1 hφ.2
    have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hφ.1,Real.pi_pos],hφ.2.le.trans hbhalf⟩
    have hp : 0 ≤ (2*Real.cos φ)^n :=
      pow_nonneg (mul_nonneg (by norm_num) hcos) _
    have hu : 0 ≤ refinedAffineU W ^ n := by
      dsimp [refinedAffineU]
      positivity
    have hbase : (2*refinedAffineU W*Real.cos φ)^n =
        (2*Real.cos φ)^n*refinedAffineU W^n := by
      calc
        _ = ((2*Real.cos φ)*refinedAffineU W)^n := by ring
        _ = _ := by rw [mul_pow]
    have hfactor := refinedAffine_amplification_le n hW0 hW hWsq
    change (1+(71/5000:ℝ)*W)*refinedAffineU W^n*
      Real.sqrt (refinedAffineU W/refinedAffineV W) ≤ amp at hfactor
    have hderivmul := mul_le_mul_of_nonneg_left hderiv hu
    have hcost : refinedAffineU W^n *
        deriv (refinedAffineAngle γ) φ ≤ amp := by
      nlinarith [hderivmul,hfactor]
    dsimp [f,g]
    rw [hprofile,hbase]
    nlinarith [mul_le_mul_of_nonneg_left hcost hp]
  have hfcont : Continuous f := by
    dsimp [f]
    have hr : Continuous (refinedAffineRadius W) := by
      unfold refinedAffineRadius
      fun_prop
    fun_prop (disch := exact hr)
  have hgcont : Continuous g := by dsimp [g,amp]; fun_prop
  have hleft : IntervalIntegrable
      (fun φ => f (refinedAffineAngle γ φ)*
        deriv (refinedAffineAngle γ) φ) volume 0 b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hb0
    exact (hfcont.comp (refinedAffine_angle_continuous γ)).continuousOn.mul
      (refinedAffine_angle_deriv_continuousOn hW0 hW)
  have hright : IntervalIntegrable g volume 0 b :=
    hgcont.intervalIntegrable _ _
  have hfirst : (∫ θ in (0:ℝ)..refinedAffineAlpha W, f θ) ≤
      ∫ φ in (0:ℝ)..b, g φ := by
    rw [hsub]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hb0 hleft hright hpoint
  have hsecond : (∫ φ in (0:ℝ)..b, g φ) ≤
      ∫ φ in (0:ℝ)..Real.pi/2, g φ := by
    apply intervalIntegral.integral_mono_interval le_rfl hb0 hbhalf
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with φ hφ
      have hcos : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hφ.1],hφ.2⟩
      dsimp [g,amp]
      positivity
    · exact hgcont.intervalIntegrable _ _
  have hfull : (∫ φ in (0:ℝ)..Real.pi/2, g φ) =
      (2:ℝ)^n*halfCosMoment n*amp := by
    dsimp [g]
    rw [intervalIntegral.integral_mul_const]
    have hpointpow (φ : ℝ) : (2*Real.cos φ)^n =
        (2:ℝ)^n*Real.cos φ^n := mul_pow _ _ _
    simp_rw [hpointpow]
    rw [intervalIntegral.integral_const_mul]
    change ((2:ℝ)^n*halfCosMoment n)*amp = _
    ring
  exact hfirst.trans (hsecond.trans_eq hfull)

/-- The normalized one-end refined affine circle cost. The comparison
cosine moment has no factor `2⁻ⁿ`; its positive half contributes `I_n/2`. -/
theorem refinedAffineModelCircle_le
    (n : ℕ) {W : ℝ} (hW0 : 0 ≤ W) (hW : W ≤ 1/500)
    (hWsq : (n:ℝ)*W^2 ≤ 3/500) :
    Real.circleAverage
      (fun ζ : ℂ => refinedAffineRadius W (2*ζ.re)^n) 0 1 ≤
      (19/10:ℝ)^n+
        (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2)*
          (1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2) := by
  let f : ℝ → ℝ := fun θ => refinedAffineRadius W (2*Real.cos θ)^n
  let amp : ℝ := 1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2
  let I : ℝ := Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  have hfcont : Continuous f := by
    dsimp [f]
    have hr : Continuous (refinedAffineRadius W) := by
      unfold refinedAffineRadius
      fun_prop
    fun_prop (disch := exact hr)
  obtain ⟨hα0,hαhalf,_,_,_,_⟩ :=
    refinedAffine_active_endpoint_angles hW0 hW
  have hαπ : refinedAffineAlpha W ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hfull := evenCos_circleAverage_eq_integral
    (fun x : ℝ => refinedAffineRadius W x^n)
    (by
      have hr : Continuous (refinedAffineRadius W) := by
        unfold refinedAffineRadius
        fun_prop
      exact hr.pow n)
  have hsplit :
      (∫ θ in (0:ℝ)..Real.pi, f θ) =
        (∫ θ in (0:ℝ)..refinedAffineAlpha W, f θ) +
          (∫ θ in refinedAffineAlpha W..Real.pi, f θ) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hfcont.intervalIntegrable _ _)
      (hfcont.intervalIntegrable _ _)).symm
  have hplate :
      (∫ θ in refinedAffineAlpha W..Real.pi, f θ) =
        (Real.pi-refinedAffineAlpha W)*(19/10:ℝ)^n := by
    have hcongr :
        (∫ θ in refinedAffineAlpha W..Real.pi, f θ) =
          ∫ θ in refinedAffineAlpha W..Real.pi, (19/10:ℝ)^n := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Set.Icc (refinedAffineAlpha W) Real.pi := by
        simpa [Set.uIcc_of_le hαπ] using hθ
      exact congrArg (fun x : ℝ => x^n)
        (refinedAffine_profile_platform hW0 hW hθ'.1 hθ'.2)
    rw [hcongr]
    simp
  have hactive := refinedAffine_active_integral_le n hW0 hW hWsq
  have hI := comparisonCircleMoment_eq_halfCosMoment n
  have hpi : 0 < Real.pi := Real.pi_pos
  have hactive' :
      (1/Real.pi)*(∫ θ in (0:ℝ)..refinedAffineAlpha W, f θ) ≤
        (I/2)*amp := by
    have hh := mul_le_mul_of_nonneg_left hactive
      (show 0 ≤ 1/Real.pi by positivity)
    change (1/Real.pi)*(∫ θ in (0:ℝ)..refinedAffineAlpha W,
      f θ) ≤ _ at hh
    change (1/Real.pi)*(∫ θ in (0:ℝ)..refinedAffineAlpha W,
      f θ) ≤
        (Real.circleAverage (fun ζ : ℂ => |2*ζ.re|^n) 0 1 / 2)*
          (1+(57/100:ℝ)*W+(55/100:ℝ)*(n:ℝ)*W^2)
    rw [hI]
    convert hh using 1 <;> ring
  have hplatform :
      (1/Real.pi)*((Real.pi-refinedAffineAlpha W)*(19/10:ℝ)^n) ≤
        (19/10:ℝ)^n := by
    have hfrac : (Real.pi-refinedAffineAlpha W)/Real.pi ≤ 1 :=
      (div_le_one hpi).2 (by linarith)
    have hh := mul_le_mul_of_nonneg_right hfrac
      (pow_nonneg (by norm_num : (0:ℝ) ≤ 19/10) n)
    convert hh using 1 <;> ring
  rw [hfull]
  change (1/Real.pi)*(∫ θ in (0:ℝ)..Real.pi, f θ) ≤
    (19/10:ℝ)^n+(I/2)*amp
  rw [hsplit,hplate,mul_add]
  linarith

end SpringerLean

#print axioms SpringerLean.refinedAffine_sqrt_inv_gamma
#print axioms SpringerLean.refinedAffine_angle_deriv_bound
#print axioms SpringerLean.refinedAffine_active_integral_le
#print axioms SpringerLean.refinedAffineModelCircle_le
