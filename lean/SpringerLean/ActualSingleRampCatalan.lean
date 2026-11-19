import SpringerLean.SingleRampAngularComparison
import SpringerLean.Round1840ActualStrictSignedComparison
import SpringerLean.Round93FourthModes

open MeasureTheory Metric
open scoped ComplexConjugate

namespace SpringerLean.AnalyticRevision

set_option maxHeartbeats 1600000

/-- The exact signed comparison criterion and the SAME actual endpoint
data now share the coefficient-selected phase. The candidate includes
equality and the reference is the actual positive-part disk integral. -/
theorem exteriorInverseCoeff_candidate_exists_signed_phase_data
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ∃ beta : ℂ, ‖beta‖=1 ∧ Nonempty (ActualCandidatePhaseEndpoints F k beta) ∧
      2*comparisonPositiveDiskMoment (2*k-2) ≤
        Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z) := by
  obtain ⟨beta, hbeta, hcost⟩ :=
    exteriorInverseCoeff_candidate_exists_singleRamp_integral F hc k hk hB
  have hends := exteriorInverseCoeff_candidate_phase_endpoints_nonempty F hc k hk hB hns beta hbeta
  have href := comparisonPositiveDiskMoment_catalan (by omega : 2 ≤ k)
  rw [pow_succ] at href
  have hpow : 0 < (2 : ℝ)^(2*k-2) := by positivity
  have hratio : (catalan (k-1) : ℝ)/(2 : ℝ)^(2*k-2)=
      2*comparisonPositiveDiskMoment (2*k-2) := by
    apply (div_eq_iff hpow.ne').mpr
    nlinarith [href]
  rw [hratio] at hcost
  exact ⟨beta, hbeta, hends, hcost⟩

/-- The actual strip now discharges the angular-cone hypothesis in
the aligned near subregion. This is pointwise on the actual filling,
not a scalar test conditional on an unproved cone estimate. -/
theorem actualSignedPhaseDensity_aligned_near_le_projection
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (z : ℂ) (hz : ‖z‖ < 1) (hx : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (a : ℝ) (hay : a*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P) ≤ 3)
    (hs : ((2*k-2 : ℕ) : ℝ)*(1-(conj v*actualHarmonic F z).re/2) ≤ 7*a/5) :
    singleRampSignedDensity F k beta z ≤
      (max ((conj v*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let w := actualHarmonic F z
  let u := conj v*w
  let H := m*|u.im|/u.re
  have hx0 : 0 < u.re := by dsimp [u, w]; linarith
  obtain ⟨hy0, hy1, hQ0, hs0, hH0, hquad, hslope⟩ :=
    exteriorOmitted_actualEndpoint_aligned_scaled_strip F hc k hk P hP hd ht hW v δ hv hδ
      w (actualHarmonic_mem_convexHull_omitted F hc hz) hx
  have hnear := aligned_strip_near_angle hk hy0 hQ0 hH0 hquad hs hay hslope
  have hm0 : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < 2*k-2)
  have hrewrite : (k : ℝ)*H/m=(k : ℝ)*(|u.im|/u.re) := by
    dsimp [H]
    field_simp
  change (k : ℝ)*H/m < 14/5 at hnear
  rw [hrewrite] at hnear
  have harg := mul_le_mul_of_nonneg_left (complex_arg_abs_le_slope hx0) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hangle : |(k : ℝ)*Complex.arg u| ≤ 14/5 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact harg.trans hnear.le
  have hnorm : ‖u‖=‖w‖ := by dsimp [u]; rw [norm_mul, Complex.norm_conj, hvunit, one_mul]
  have hwpos : 0 < ‖w‖ := by
    have hh := Complex.re_le_norm u
    rw [hnorm] at hh
    exact hx0.trans_le hh
  exact actualSignedPhaseDensity_le_projected_of_aligned_polar F beta v z hvunit k hk
    hphase hwpos (unit_direction_polar v w hvunit) hangle hx0.le

/-- In the far aligned subregion the lower power controls even the
unsigned actual moment density. This branch needs no phase saving. -/
theorem actualSignedPhaseDensity_aligned_far_lt_lower_power
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (z : ℂ) (hz : ‖z‖ < 1) (hx : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (a : ℝ) (ha : 6 ≤ a)
    (hs : 7*a/5 ≤ ((2*k-2 : ℕ) : ℝ)*(1-(conj v*actualHarmonic F z).re/2)) :
    singleRampSignedDensity F k beta z <
      (2*(1-a/((2*k-2 : ℕ) : ℝ)))^8*
        (max ((conj v*actualHarmonic F z).re) 0)^(2*k-10)/(2 : ℝ)^(2*k-2) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let w := actualHarmonic F z
  let x := (conj v*w).re
  let s := m*(1-x/2)
  have hx0 : 0 < x := by dsimp [x, w]; linarith
  have hm0 : 0 < m := by dsimp [m]; exact_mod_cast (by omega : 0 < 2*k-2)
  obtain ⟨hy0, hy1, hQ0, hs0, hH0, hquad, hslope⟩ :=
    exteriorOmitted_actualEndpoint_aligned_scaled_strip F hc k hk P hP hd ht hW v δ hv hδ
      w (actualHarmonic_mem_convexHull_omitted F hc hz) hx
  have hfar := aligned_strip_far_cost hy0 hy1 hQ0 hs0 ha hs hH0 hslope hquad
  have has : a ≤ s := by change 7*a/5 ≤ s at hs; linarith
  have hsm : s < m := by
    dsimp [s]
    nlinarith [mul_pos hm0 hx0]
  have hmn : m=2*((k-1 : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast (by omega : 2*k-2=2*(k-1))
  have hxs : x=2*(1-s/(2*((k-1 : ℕ) : ℝ))) := by
    rw [←hmn]
    dsimp [s]
    field_simp
    <;> ring
  have hcost : (2*((k-1 : ℕ) : ℝ))^2*(|(conj v*w).im|/x)^2/2 < 8*(s-a) := by
    rw [←hmn]
    change (m*|(conj v*w).im|/x)^2/2 < 8*(s-a) at hfar
    convert hfar using 1 <;> ring
  have hp := far_complex_power_le_lower_test (k-1) (by omega : 4 ≤ k-1) v w hvunit
    (by linarith : 0 ≤ a) has (by rw [←hmn]; exact hsm) hx0 hxs hcost
  have hexp : 2*(k-1)=2*k-2 := by omega
  have hexp' : 2*k-2-8=2*k-10 := by omega
  rw [hexp, hexp', ←hmn] at hp
  have hpot : 0 ≤ actualHarmonicPhasePotentialDensity F k beta z := by
    unfold actualHarmonicPhasePotentialDensity
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hraw : ‖w‖^(2*k-2)-(3/14 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z ≤
      ‖w‖^(2*k-2) := by nlinarith
  unfold singleRampSignedDensity
  rw [max_eq_left hx0.le]
  exact (div_le_div_of_nonneg_right hraw (by positivity)).trans_lt
    (div_lt_div_of_pos_right hp (by positivity))

/-- Full actual aligned pointwise comparison, combining the near
phase penalty and far unsigned lower-power branches. -/
theorem actualSignedPhaseDensity_aligned_le_twoPower
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |(k : ℝ)*δ| ≤ Real.pi/3)
    (z : ℂ) (hz : ‖z‖ < 1) (hx : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (a : ℝ) (ha : 6 ≤ a)
    (hay : a*(((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P) ≤ 3) :
    singleRampSignedDensity F k beta z ≤
      twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
        ((conj v*actualHarmonic F z).re)/(2 : ℝ)^(2*k-2) := by
  have hi : 2*k-12+10=2*k-2 := by omega
  have hi' : 2*k-12+2=2*k-10 := by omega
  have hfirst : (max ((conj v*actualHarmonic F z).re) 0)^(2*k-2) ≤
      twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
        ((conj v*actualHarmonic F z).re) := by
    unfold twoPowerPhaseTest
    rw [hi, hi']
    exact le_max_left _ _
  have hsecond : (2*(1-a/((2*k-2 : ℕ) : ℝ)))^8*
      (max ((conj v*actualHarmonic F z).re) 0)^(2*k-10) ≤
      twoPowerPhaseTest (2*(1-a/((2*k-2 : ℕ) : ℝ))) (2*k-12)
        ((conj v*actualHarmonic F z).re) := by
    unfold twoPowerPhaseTest
    rw [hi, hi']
    exact le_max_right _ _
  by_cases hs : ((2*k-2 : ℕ) : ℝ)*(1-(conj v*actualHarmonic F z).re/2) ≤ 7*a/5
  · exact (actualSignedPhaseDensity_aligned_near_le_projection F hc k hk P hP hd ht hW
      beta v hvunit hphase δ hv hδ z hz hx a hay hs).trans
        (div_le_div_of_nonneg_right hfirst (by positivity))
  · have hfar := actualSignedPhaseDensity_aligned_far_lt_lower_power F hc k hk P hP hd ht hW
      beta v hvunit δ hv hδ z hz hx a ha (le_of_lt (lt_of_not_ge hs))
    exact hfar.le.trans (div_le_div_of_nonneg_right hsecond (by positivity))

/-- Actual nonaligned pointwise comparison in the true endpoint axis.
The actual strip controls the angular cost, the recorded phase ray
supplies its phase, and the fixed moment-ratio factor pays for it. -/
theorem actualSignedPhaseDensity_trueAxis_lt_lower_power
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδlo : Real.pi/3 ≤ |(k : ℝ)*δ|) (hδhi : |(k : ℝ)*δ| ≤ Real.pi/2)
    (z : ℂ) (hz : ‖z‖ < 1)
    (hx : (9/5 : ℝ) ≤ (conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re) :
    singleRampSignedDensity F k beta z <
      trueAxisMomentRatioLambda ((2*k-2 : ℕ) : ℝ)*
        (max ((conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re/2) 0)^(2*k-10) := by
  let m := ((2*k-2 : ℕ) : ℝ)
  let ξ := P/(‖P‖ : ℂ)
  let w := actualHarmonic F z
  let Z := conj ξ*w
  let x := Z.re
  let u := x/2
  let s := m*(1-u)
  let h := |Z.im|/x
  let gamma := (k : ℝ)*δ
  let theta := (k : ℝ)*Complex.arg Z
  let Lambda := trueAxisMomentRatioLambda m
  have hm : (1500 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hn : (1501 : ℝ) ≤ ((2*k-1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1501 ≤ 2*k-1)
  have hR : 0 < ‖P‖ := by nlinarith [mul_le_mul_of_nonneg_right hn hd.le]
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_self hR.ne']
  have hx0 : 0 < x := by dsimp [x, Z, ξ, w]; linarith
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hnorm : ‖Z‖=‖w‖ := by dsimp [Z]; rw [norm_mul, Complex.norm_conj, hξ, one_mul]
  have hx2 : x ≤ 2 := by
    calc
      x ≤ ‖Z‖ := Complex.re_le_norm _
      _ = ‖w‖ := hnorm
      _ ≤ 2 := exteriorOmitted_convexHull_norm_le_two F hc (actualHarmonic_mem_convexHull_omitted F hc hz)
  have hs0 : 0 ≤ s := mul_nonneg hm0.le (by dsimp [u]; linarith)
  obtain ⟨hcost,hshort⟩ := exteriorOmitted_actualEndpoint_trueAxis_angles F hc k hk P hP hd ht hW z hz hx
  change m^2*h^2/2 ≤ 1/6+(5/8 : ℝ)*s at hcost
  change (s ≤ 2 → |theta| ≤ 6/7) at hshort
  obtain ⟨hLambda,hlogLambda⟩ := trueAxisMomentRatioLambda_pos_and_log hm
  have hmn : m=2*((k-1 : ℕ) : ℝ) := by
    dsimp [m]
    exact_mod_cast (by omega : 2*k-2=2*(k-1))
  have hclose : s ≤ 1 → |theta| ≤ 2/3 := by
    intro hs1
    have hmk : (k : ℝ) ≤ (501/1000 : ℝ)*m := by
      have hk' : (751 : ℝ) ≤ k := by exact_mod_cast hk
      rw [hmn, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      linarith
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hscaled : (k:ℝ)*h ≤ (501/1000:ℝ)*(m*h) := by
      nlinarith [mul_le_mul_of_nonneg_right hmk hh]
    have hM : (m*h)^2 ≤ 19/12 := by nlinarith [hcost,hs1]
    have hsmall : (501/1000:ℝ)*(m*h) ≤ 2/3 := by
      by_contra! hbad
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/3) hbad.le 2]
    have harg := complex_arg_abs_le_slope hx0
    dsimp [theta]
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    exact (mul_le_mul_of_nonneg_left harg (Nat.cast_nonneg k)).trans (hscaled.trans hsmall)
  have hp := trueAxis_signed_power_lt_lower (k-1) (by omega : 750 ≤ k-1)
    hu0 hs0 (by rw [←hmn]) hLambda
    (by rw [←hmn]; exact hlogLambda) (by rw [←hmn]; exact hcost)
    hδlo hδhi hclose hshort
  have hexp : 2*(k-1)=2*k-2 := by omega
  have hexp' : 2*k-2-8=2*k-10 := by omega
  rw [hexp, hexp'] at hp
  have hr : 0 < ‖w‖ := by
    have hh := Complex.re_le_norm Z
    rw [hnorm] at hh
    exact hx0.trans_le hh
  have hpot := actualHarmonicPhasePotentialDensity_relative_polar F k (by omega : 1 ≤ k)
    beta ξ v hξ δ hv hphase z hr
  change actualHarmonicPhasePotentialDensity F k beta z=
    ‖w‖^(2*k-2)*(Real.sin (gamma-theta))^2 at hpot
  have hnorm2 : ‖w‖^2=x^2+Z.im^2 := by
    rw [←hnorm, Complex.sq_norm]
    simp only [Complex.normSq_apply, x, pow_two]
  have hf2 : ‖w‖^2=x^2*(1+h^2) := by
    rw [hnorm2]
    dsimp [h]
    rw [div_pow, sq_abs]
    field_simp [hx0.ne']
    <;> ring
  have hfraw : ‖w‖^(2*(k-1))=x^(2*(k-1))*(1+h^2)^(k-1) := by
    rw [pow_mul, hf2, mul_pow, ←pow_mul]
  have hf : ‖w‖^(2*k-2)/(2 : ℝ)^(2*k-2)=u^(2*k-2)*(1+h^2)^(k-1) := by
    rw [←hexp, hfraw]
    dsimp [u]
    conv_rhs => rw [div_pow]
    ring
  have hdensity : singleRampSignedDensity F k beta z=
      u^(2*k-2)*(1+h^2)^(k-1)*(1-(3/14 : ℝ)*(Real.sin (gamma-theta))^2) := by
    unfold singleRampSignedDensity
    rw [hpot]
    change (‖w‖^(2*k-2)-(3/14 : ℝ)*(‖w‖^(2*k-2)*(Real.sin (gamma-theta))^2))/(2 : ℝ)^(2*k-2)=_
    have heq : (‖w‖^(2*k-2)-(3/14 : ℝ)*(‖w‖^(2*k-2)*(Real.sin (gamma-theta))^2))/(2 : ℝ)^(2*k-2)=
        (‖w‖^(2*k-2)/(2 : ℝ)^(2*k-2))*(1-(3/14 : ℝ)*(Real.sin (gamma-theta))^2) := by ring
    rw [heq,hf]
  change singleRampSignedDensity F k beta z < Lambda*(max u 0)^(2*k-10)
  rw [hdensity,max_eq_left hu0.le]
  exact hp

theorem actualSignedPhaseDensity_le_endpointPhaseTest
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (P : ℂ) (hP : P ∈ exteriorOmitted F)
    (hd : 0 < 2-‖P‖) (ht : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖) < 3/20)
    (hlog : ((2*k-1 : ℕ) : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)) < 3/2)
    (hwidth : exteriorFineEndpointWidth P < (1/3 : ℝ)*(2-‖P‖)*Real.log (2/(2-‖P‖)))
    (hW : ((2*k-2 : ℕ) : ℝ)*exteriorFineEndpointWidth P < 1/2)
    (beta v : ℂ) (hvunit : ‖v‖=1) (hphase : (beta*v^k)^2=1)
    (δ : ℝ) (hv : v=(P/(‖P‖ : ℂ))*Complex.exp ((δ : ℂ)*Complex.I))
    (hδ : |δ| ≤ Real.pi/(2*(k : ℝ)))
    (z : ℂ) (hz : ‖z‖ < 1)
    (hxray : (9/5 : ℝ) ≤ (conj v*actualHarmonic F z).re)
    (hxaxis : (9/5 : ℝ) ≤ (conj (P/(‖P‖ : ℂ))*actualHarmonic F z).re) :
    singleRampSignedDensity F k beta z ≤ endpointPhaseTest k P v δ (actualHarmonic F z) := by
  unfold endpointPhaseTest
  by_cases halign : |(k : ℝ)*δ| ≤ Real.pi/3
  · rw [if_pos halign]
    obtain ⟨_,_,ha,_,hay⟩ := endpointPhaseParameter_bounds k hk P hd ht hlog hwidth
    exact actualSignedPhaseDensity_aligned_le_twoPower F hc k hk P hP hd ht hW beta v hvunit
      hphase δ hv halign z hz hxray (endpointPhaseParameter k P) ha hay
  · rw [if_neg halign]
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hupper : |(k : ℝ)*δ| ≤ Real.pi/2 := by
      rw [abs_mul,abs_of_pos hk0]
      have hh := (le_div_iff₀ (show (0 : ℝ) < 2*(k : ℝ) by positivity)).mp hδ
      nlinarith
    exact (actualSignedPhaseDensity_trueAxis_lt_lower_power F hc k hk P hP hd ht hW beta v
      hphase δ hv (le_of_lt (lt_of_not_ge halign)) hupper z hz hxaxis).le

theorem actualSignedPhaseDensity_endpointTests_outer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (z : ℂ) (hz : ‖z‖ < 1) (hr : (46/25 : ℝ) ≤ ‖actualHarmonic F z‖) :
    singleRampSignedDensity F k beta z ≤
      endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)+
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z) := by
  have hproj := ActualCandidatePhaseEndpoints.outer_projections F hc k hk beta ends
  have haxis := ActualCandidatePhaseEndpoints.outer_axis_projections F hc k hk beta ends
  have hmem := actualHarmonic_mem_convexHull_omitted F hc hz
  have hnonneg₁ := endpointPhaseTest_nonneg k hk ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)
  have hnonneg₂ := endpointPhaseTest_nonneg k hk ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)
  by_cases hforward : 0 ≤ (conj (ends.P₁/(‖ends.P₁‖ : ℂ))*actualHarmonic F z).re
  · have hh := actualSignedPhaseDensity_le_endpointPhaseTest F hc k hk ends.P₁ ends.mem₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ ends.scaled_width₁
      beta ends.v₁ ends.unit₁ ends.phase₁ ends.θ₁ ends.ray₁ ends.angle₁ z hz
      (hproj.1 _ hmem hr hforward).le (haxis.1 _ hmem hr hforward).le
    linarith
  · have hback := le_of_lt (lt_of_not_ge hforward)
    have hh := actualSignedPhaseDensity_le_endpointPhaseTest F hc k hk ends.P₂ ends.mem₂
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.log_localization₂ ends.fine_width₂ ends.scaled_width₂
      beta ends.v₂ ends.unit₂ ends.phase₂ ends.θ₂ ends.ray₂ ends.angle₂ z hz
      (hproj.2 _ hmem hr hback).le (haxis.2 _ hmem hr hback).le
    linarith

theorem actualSignedPhaseDensity_endpointTests_global
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (z : ℂ) (hz : ‖z‖ < 1) :
    singleRampSignedDensity F k beta z ≤
      endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)+
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)+(23/25 : ℝ)^(2*k-2) := by
  by_cases hr : (46/25 : ℝ) ≤ ‖actualHarmonic F z‖
  · have hh := actualSignedPhaseDensity_endpointTests_outer F hc k hk beta ends z hz hr
    linarith [show 0 ≤ (23/25 : ℝ)^(2*k-2) by positivity]
  · have hfrac : ‖actualHarmonic F z‖/2 ≤ (23/25 : ℝ) := by linarith
    have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ ‖actualHarmonic F z‖/2) hfrac (2*k-2)
    rw [div_pow] at hpower
    have hpot : 0 ≤ actualHarmonicPhasePotentialDensity F k beta z := by
      unfold actualHarmonicPhasePotentialDensity
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hraw : ‖actualHarmonic F z‖^(2*k-2)-(3/14 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z ≤
        ‖actualHarmonic F z‖^(2*k-2) := by nlinarith
    have hsigned := div_le_div_of_nonneg_right hraw (by positivity : 0 ≤ (2 : ℝ)^(2*k-2))
    change singleRampSignedDensity F k beta z ≤ _ at hsigned
    have hnonneg₁ := endpointPhaseTest_nonneg k hk ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)
    have hnonneg₂ := endpointPhaseTest_nonneg k hk ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)
    linarith

/-- The actual disk comparison now covers every recorded phase.
The central allowance is counted once, independently of the two tests. -/
theorem actualSignedPhaseIntegral_endpointTests_le
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z) ≤
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
        endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z))+
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z))+
      (23/25 : ℝ)^(2*k-2) := by
  have hS := singleRampSignedDensity_integrableOn F hc (by omega : 1 ≤ k) beta hbeta
  obtain ⟨hP₁,hP₂⟩ := ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends
  have h₁ := endpointPhaseTest_actual_integrableOn F hc k ends.P₁ ends.v₁ ends.θ₁ ends.unit₁ hP₁
  have h₂ := endpointPhaseTest_actual_integrableOn F hc k ends.P₂ ends.v₂ ends.θ₂ ends.unit₂ hP₂
  have hC : IntegrableOn (fun _z : ℂ => (23/25 : ℝ)^(2*k-2)) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ continuousOn_const
      ‖(23/25 : ℝ)^(2*k-2)‖ (fun _ _ => le_refl _)
  have hpoint : (fun z => singleRampSignedDensity F k beta z) ≤ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      (fun z => endpointPhaseTest k ends.P₁ ends.v₁ ends.θ₁ (actualHarmonic F z)+
        endpointPhaseTest k ends.P₂ ends.v₂ ends.θ₂ (actualHarmonic F z)+(23/25 : ℝ)^(2*k-2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
    exact actualSignedPhaseDensity_endpointTests_global F hc k hk beta ends z
      (by simpa only [mem_ball,dist_zero_right] using hz)
  have hi := integral_mono_ae hS ((h₁.add h₂).add hC) hpoint
  have hn := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ Real.pi⁻¹)
  have hsum := integral_add (h₁.add h₂) hC
  simp only [Pi.add_apply] at hn hsum
  rw [hsum, integral_add h₁ h₂] at hn
  have hconst := normalized_unitDisk_integral_const ((23/25 : ℝ)^(2*k-2))
  nlinarith

/-- A variable central allowance, valid on the actual full source
disk; the same first endpoint supplies both antipodal phase rays. -/
theorem actualSignedPhaseDensity_antipodal_global
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (z : ℂ) (hz : ‖z‖ < 1) :
    let E := (2-‖ends.P₁‖)*Real.log (2/(2-‖ends.P₁‖))
    singleRampSignedDensity F k beta z ≤
      antipodalPhaseTest k ends.v₁ (actualHarmonic F z)+
        (3*(k : ℝ)*Real.sqrt E)^(2*k-2) := by
  let E := (2-‖ends.P₁‖)*Real.log (2/(2-‖ends.P₁‖))
  let ξ := ends.P₁/(‖ends.P₁‖ : ℂ)
  let w := actualHarmonic F z
  have hL := (endpointPhaseParameter_scalar_relations k hk ends.P₁ ends.deficit_pos₁ ends.scaled_deficit₁).1
  have hE : 0 < E := by
    have hL0 : 0 < Real.log (2/(2-‖ends.P₁‖)) := by linarith
    exact mul_pos ends.deficit_pos₁ hL0
  have hP := (ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends).1
  have hξ : ‖ξ‖=1 := by
    dsimp [ξ]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hP,div_self hP.ne']
  have htrans := exteriorOmitted_actualEndpoint_transverse_le_deficit F hc k hk ends.P₁ ends.mem₁
    ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ w
    (actualHarmonic_mem_convexHull_omitted F hc hz)
  change |(conj ξ*w).im| ≤ (5/2 : ℝ)*Real.sqrt E at htrans
  have htest := antipodalPhaseTest_nonneg k ends.v₁ w
  change singleRampSignedDensity F k beta z ≤ antipodalPhaseTest k ends.v₁ w+(3*(k : ℝ)*Real.sqrt E)^(2*k-2)
  by_cases houter : 6*(k : ℝ)*Real.sqrt E < ‖w‖
  · have hr0 : 0 < ‖w‖ := (show 0 < 6*(k : ℝ)*Real.sqrt E by positivity).trans houter
    have hpoint : singleRampSignedDensity F k beta z ≤ antipodalPhaseTest k ends.v₁ w := by
      by_cases hforward : 0 ≤ (conj ξ*w).re
      · obtain ⟨θ,hw,hθ,hproj⟩ := unit_perturbed_axis_tiny_outer_cone k hk hE ξ ends.v₁ w hξ
          ends.unit₁ ends.θ₁ ends.ray₁ ends.angle₁ hforward htrans houter
        have hh := actualSignedPhaseDensity_le_projected_of_aligned_polar F beta ends.v₁ z ends.unit₁ k hk
          ends.phase₁ hr0 hw hθ hproj.le
        unfold antipodalPhaseTest
        linarith [show 0 ≤ (max ((conj (-ends.v₁)*w).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) by positivity]
      · have hforward' : 0 ≤ (conj (-ξ)*w).re := by
          simp only [map_neg,neg_mul,Complex.neg_re]
          linarith
        have htrans' : |(conj (-ξ)*w).im| ≤ (5/2 : ℝ)*Real.sqrt E := by
          simpa only [map_neg,neg_mul,Complex.neg_im,abs_neg] using htrans
        have hray : -ends.v₁=(-ξ)*Complex.exp ((ends.θ₁ : ℂ)*Complex.I) := by
          rw [ends.ray₁]
          ring
        obtain ⟨θ,hw,hθ,hproj⟩ := unit_perturbed_axis_tiny_outer_cone k hk hE (-ξ) (-ends.v₁) w
          (by simpa only [norm_neg] using hξ) (by simpa only [norm_neg] using ends.unit₁)
          ends.θ₁ hray ends.angle₁ hforward' htrans' houter
        have hh := actualSignedPhaseDensity_le_projected_of_aligned_polar F beta (-ends.v₁) z
          (by simpa only [norm_neg] using ends.unit₁) k hk
          (phase_square_antipode beta ends.v₁ k ends.phase₁) hr0 hw hθ hproj.le
        unfold antipodalPhaseTest
        linarith [show 0 ≤ (max ((conj ends.v₁*w).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2) by positivity]
    exact hpoint.trans (le_add_of_nonneg_right (by positivity))
  · have hsmall : ‖w‖/2 ≤ 3*(k : ℝ)*Real.sqrt E := by linarith
    have hpower := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖/2) hsmall (2*k-2)
    rw [div_pow] at hpower
    have hpot : 0 ≤ actualHarmonicPhasePotentialDensity F k beta z := by
      unfold actualHarmonicPhasePotentialDensity
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hraw : ‖w‖^(2*k-2)-(3/14 : ℝ)*actualHarmonicPhasePotentialDensity F k beta z ≤ ‖w‖^(2*k-2) := by nlinarith
    have hsigned := div_le_div_of_nonneg_right hraw (by positivity : 0 ≤ (2 : ℝ)^(2*k-2))
    change singleRampSignedDensity F k beta z ≤ _ at hsigned
    linarith

/-- Both real antipodal gains are retained at the SAME first-endpoint
deficit. Only the explicit vanishing central scalar remains. -/
theorem actualSignedPhaseIntegral_antipodal_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    let m := ((2*k-2 : ℕ) : ℝ)
    let d := 2-‖ends.P₁‖
    let E := d*Real.log (2/d)
    m*Real.sqrt m*(Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1,
      singleRampSignedDensity F k beta z)-2*comparisonPositiveDiskMoment (2*k-2)) <
      m*Real.sqrt m*(3*(k : ℝ)*Real.sqrt E)^(2*k-2)-(m*d)^3/15 := by
  let E := (2-‖ends.P₁‖)*Real.log (2/(2-‖ends.P₁‖))
  let C := (3*(k : ℝ)*Real.sqrt E)^(2*k-2)
  have hS := singleRampSignedDensity_integrableOn F hc (by omega : 1 ≤ k) beta hbeta
  have hA := antipodalPhaseTest_actual_integrableOn F hc k ends.v₁ ends.unit₁
  have hC : IntegrableOn (fun _z : ℂ => C) (ball (0 : ℂ) 1) :=
    integrableOn_unitDisk_of_continuousOn_bound _ continuousOn_const ‖C‖ (fun _ _ => le_refl _)
  have hpoint : (fun z => singleRampSignedDensity F k beta z) ≤ᵐ[volume.restrict (ball (0 : ℂ) 1)]
      (fun z => antipodalPhaseTest k ends.v₁ (actualHarmonic F z)+C) := by
    filter_upwards [ae_restrict_mem (measurableSet_ball : MeasurableSet (ball (0 : ℂ) 1))] with z hz
    exact actualSignedPhaseDensity_antipodal_global F hc k hk beta ends z
      (by simpa only [mem_ball,dist_zero_right] using hz)
  have hi := integral_mono_ae hS (hA.add hC) hpoint
  have hn := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ Real.pi⁻¹)
  have hsum := integral_add hA hC
  simp only [Pi.add_apply] at hn hsum
  rw [hsum] at hn
  have hconst := normalized_unitDisk_integral_const C
  have h₁ := actualHarmonic_projection_test_integrableOn F hc ends.v₁ ends.unit₁
    (fun x : ℝ => (max x 0)^(2*k-2)/(2 : ℝ)^(2*k-2)) (by fun_prop)
  have h₂ := actualHarmonic_projection_test_integrableOn F hc (-ends.v₁) (by simpa only [norm_neg] using ends.unit₁)
    (fun x : ℝ => (max x 0)^(2*k-2)/(2 : ℝ)^(2*k-2)) (by fun_prop)
  have htestsum := integral_add h₁ h₂
  unfold antipodalPhaseTest at hn
  rw [htestsum] at hn
  have hs₁ := actualDirectionalPowerSaving_integral_identity F hc (2*k-2) ends.v₁ ends.unit₁
  have hs₂ := actualDirectionalPowerSaving_integral_identity F hc (2*k-2) (-ends.v₁)
    (by simpa only [norm_neg] using ends.unit₁)
  have hgain := ActualCandidatePhaseEndpoints.first_all_direction_gains F hc k hk beta ends
  have hg₁ := hgain ends.v₁ ends.unit₁
  have hg₂ := hgain (-ends.v₁) (by simpa only [norm_neg] using ends.unit₁)
  rw [←hs₁] at hg₁
  rw [←hs₂] at hg₂
  have hcost : Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z) ≤
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max ((conj ends.v₁*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2))+
      Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, (max ((conj (-ends.v₁)*actualHarmonic F z).re) 0)^(2*k-2)/(2 : ℝ)^(2*k-2))+C := by
    nlinarith [hn,hconst]
  have hh := mul_le_mul_of_nonneg_left hcost
    (show 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) by positivity)
  dsimp only
  dsimp [C,E] at hconst hh
  nlinarith [hh,hg₁,hg₂]

theorem actualSignedPhaseIntegral_endpoint_phase_budget
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    let m := ((2*k-2 : ℕ) : ℝ)
    m*Real.sqrt m*(Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z)-
      2*comparisonPositiveDiskMoment (2*k-2)) ≤
      endpointPhaseBudget k ends.P₁ ends.θ₁+endpointPhaseBudget k ends.P₂ ends.θ₂+
        m*Real.sqrt m*(23/25 : ℝ)^(2*k-2) := by
  obtain ⟨hP₁,hP₂⟩ := ActualCandidatePhaseEndpoints.radius_pos F k hk beta ends
  have h₁ := endpointPhaseTest_actual_integral_budget F hc k hk ends.P₁ ends.v₁ ends.θ₁ ends.unit₁ hP₁ ends.saving₁
  have h₂ := endpointPhaseTest_actual_integral_budget F hc k hk ends.P₂ ends.v₂ ends.θ₂ ends.unit₂ hP₂ ends.saving₂
  have hi := actualSignedPhaseIntegral_endpointTests_le F hc k hk beta hbeta ends
  have hh := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) by positivity)
  dsimp only
  nlinarith [hh,h₁,h₂]

theorem actualSignedPhaseIntegral_tiny_first_strict
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta)
    (htiny : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) <
      (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ)))) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z) <
      2*comparisonPositiveDiskMoment (2*k-2) := by
  let mn := 2*k-2
  let m := (mn : ℝ)
  let d := 2-‖ends.P₁‖
  have hm : (1500 : ℝ) ≤ m := by dsimp [m,mn]; exact_mod_cast (by omega : 1500 ≤ 2*k-2)
  have hm0 : 0 < m := by linarith
  have hd : 0 < d := ends.deficit_pos₁
  have hX : 0 < Real.log (100*m) := Real.log_pos (by nlinarith)
  have hsmall : d ≤ (3/100 : ℝ)/(m^2*Real.log (100*m)) := by
    change m*d < (3/100 : ℝ)/(m*Real.log (100*m)) at htiny
    apply (le_div_iff₀ (by positivity : 0 < m^2*Real.log (100*m))).mpr
    have hh := (lt_div_iff₀ (mul_pos hm0 hX)).mp htiny
    nlinarith
  have hL := (endpointPhaseParameter_scalar_relations k hk ends.P₁ ends.deficit_pos₁ ends.scaled_deficit₁).1
  have hs := tiny_central_cost_lt_cubic k hk hd hL.le hsmall
  have hb := actualSignedPhaseIntegral_antipodal_budget F hc k hk beta hbeta ends
  have hN : 0 < m*Real.sqrt m := by positivity
  apply lt_of_not_ge
  intro hcost
  have hnonneg := mul_nonneg hN.le (sub_nonneg.mpr hcost)
  dsimp only at hs hb
  change 0 ≤ ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ)*
    (Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z)-
      2*comparisonPositiveDiskMoment (2*k-2)) at hnonneg
  nlinarith [hs,hb,hnonneg]

/-- Every positive-deficit actual endpoint configuration has signed
cost strictly below the Catalan reference. All phase cases included. -/
theorem actualSignedPhaseIntegral_lt_two_reference
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) (beta : ℂ) (hbeta : ‖beta‖=1)
    (ends : ActualCandidatePhaseEndpoints F k beta) :
    Real.pi⁻¹*(∫ z in ball (0 : ℂ) 1, singleRampSignedDensity F k beta z) <
      2*comparisonPositiveDiskMoment (2*k-2) := by
  by_cases htiny : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) <
      (3/100 : ℝ)/(((2*k-2 : ℕ) : ℝ)*Real.log (100*((2*k-2 : ℕ) : ℝ)))
  · exact actualSignedPhaseIntegral_tiny_first_strict F hc k hk beta hbeta ends htiny
  · have hcut₁ := le_of_not_gt htiny
    have hR := ends.first_max ends.P₂ (subset_convexHull ℝ (exteriorOmitted F) ends.mem₂)
    have hD : ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₁‖) ≤ ((2*k-2 : ℕ) : ℝ)*(2-‖ends.P₂‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    have hcut₂ := hcut₁.trans hD
    have h₁ := endpointPhaseBudget_add_center_neg_of_nonTiny k hk ends.P₁ ends.θ₁
      ends.deficit_pos₁ ends.scaled_deficit₁ ends.log_localization₁ ends.fine_width₁ hcut₁
    have h₂ := endpointPhaseBudget_add_center_neg_of_nonTiny k hk ends.P₂ ends.θ₂
      ends.deficit_pos₂ ends.scaled_deficit₂ ends.log_localization₂ ends.fine_width₂ hcut₂
    have hb := actualSignedPhaseIntegral_endpoint_phase_budget F hc k hk beta hbeta ends
    have hm0 : (0 : ℝ) < ((2*k-2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2*k-2)
    have hN : 0 < ((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ) := by positivity
    have hcenter : 0 ≤ (((2*k-2 : ℕ) : ℝ)*Real.sqrt ((2*k-2 : ℕ) : ℝ))*(23/25 : ℝ)^(2*k-2) := by positivity
    apply lt_of_not_ge
    intro hcost
    have hnonneg := mul_nonneg hN.le (sub_nonneg.mpr hcost)
    dsimp only at hb
    linarith

theorem exteriorInverseCoeff_candidate_nonslit_false
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hB : (catalan (k-1) : ℝ) ≤ ‖exteriorInverseCoeff F (2*k-1)‖)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) : False := by
  obtain ⟨beta,hbeta,⟨ends⟩,hcost⟩ := exteriorInverseCoeff_candidate_exists_signed_phase_data F hc k hk hB hns
  exact (not_lt_of_ge hcost) (actualSignedPhaseIntegral_lt_two_reference F hc k hk beta hbeta ends)

theorem exteriorInverseCoeff_large_lt_catalan_of_nonslit
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k)
    (hns : ¬ ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) :
    ‖exteriorInverseCoeff F (2*k-1)‖ < (catalan (k-1) : ℝ) := by
  apply lt_of_not_ge
  intro hB
  exact exteriorInverseCoeff_candidate_nonslit_false F hc k hk hB hns

/-- The original-hypothesis large-order theorem, sharp upper bound
and complete fixed-order equality classification on the OPEN exterior
disk. No candidate, energy, certificate or endpoint premise remains. -/
theorem exteriorInverseCoeff_large_catalan_and_eq_iff_slit_singleRamp
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    (k : ℕ) (hk : 751 ≤ k) :
    ‖exteriorInverseCoeff F (2*k-1)‖ ≤ (catalan (k-1) : ℝ) ∧
      (‖exteriorInverseCoeff F (2*k-1)‖ = (catalan (k-1) : ℝ) ↔
        ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk) := by
  by_cases hslit : ∃ a : ℂ, ‖a‖=1 ∧ Set.EqOn F (slitMap a) exteriorDisk
  · obtain ⟨a,ha,hEq⟩ := hslit
    have heq := exteriorInverseCoeff_sharp_of_eqOn_slit_all_orders F hc a ha hEq k (by omega : 1 ≤ k)
    exact ⟨heq.le,⟨fun _ => ⟨a,ha,hEq⟩,fun _ => heq⟩⟩
  · have hh := exteriorInverseCoeff_large_lt_catalan_of_nonslit F hc k hk hslit
    exact ⟨hh.le,⟨fun heq => False.elim ((ne_of_lt hh) heq),fun hs => False.elim (hslit hs)⟩⟩

end SpringerLean.AnalyticRevision

#print axioms SpringerLean.AnalyticRevision.exteriorInverseCoeff_large_catalan_and_eq_iff_slit_singleRamp
