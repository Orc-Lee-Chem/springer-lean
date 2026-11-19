import SpringerLean.Round1767TwoPowerPolynomial

namespace SpringerLean
noncomputable section
set_option maxHeartbeats 800000

def twoPowerPhaseTest (R : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  max ((max x 0)^(j+10)) (R^8*(max x 0)^(j+2))

/-- The two-power test retains the exact lower/upper curvature ratio.
The conclusion is global, so the existing actual convex-order theorem
can be used without extending a test from a compact interval. -/
theorem twoPowerPhaseTest_sub_power_convexOn {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    ConvexOn ℝ Set.univ (fun x : ℝ =>
      twoPowerPhaseTest R j x-phasePowerRetention j*(max x 0)^(j+10)) := by
  let κ := phasePowerRetention j
  let P := phaseLowerPolynomial R j
  let L := phaseLowerPolynomialDeriv R j R
  let left : ℝ → ℝ := fun x => P (max x 0)-L*x
  let right : ℝ → ℝ := fun x => (1-κ)*x^(j+10)-L*x
  have hk := phasePowerRetention_bounds j
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hL : 0 ≤ L := (phaseLowerPolynomial_deriv_bounds hR hR le_rfl j).1
  have hconv := phaseLowerPolynomial_convexOn hR j
  have hmono := phaseLowerPolynomial_monotoneOn hR j
  have hdermono := phaseLowerPolynomialDeriv_monotoneOn hR j
  have hleftConv : ConvexOn ℝ (Set.Iic R) left := by
    refine ⟨convex_Iic R, ?_⟩
    intro x hx y hy a b ha hb hab
    have hx' : max x 0 ∈ Set.Icc 0 R := ⟨le_max_right _ _, max_le hx hR⟩
    have hy' : max y 0 ∈ Set.Icc 0 R := ⟨le_max_right _ _, max_le hy hR⟩
    have hcombo : a*max x 0+b*max y 0 ∈ Set.Icc 0 R := by
      simpa only [smul_eq_mul] using hconv.1 hx' hy' ha hb hab
    have hab' : max (a*x+b*y) 0 ≤ a*max x 0+b*max y 0 := by
      apply max_le
      · nlinarith [mul_le_mul_of_nonneg_left (le_max_left x 0) ha,
          mul_le_mul_of_nonneg_left (le_max_left y 0) hb]
      · positivity
    have hz : max (a*x+b*y) 0 ∈ Set.Icc 0 R :=
      ⟨le_max_right _ _, hab'.trans hcombo.2⟩
    have h1 := hmono hz hcombo hab'
    have h2 := hconv.2 hx' hy' ha hb hab
    simp only [smul_eq_mul] at h2 ⊢
    dsimp [left]
    nlinarith
  have hantiP : AntitoneOn (fun x => P x-L*x) (Set.Icc 0 R) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 R)
      (show ContinuousOn (fun x => P x-L*x) _ by dsimp [P]; unfold phaseLowerPolynomial; fun_prop)
      (fun x _ => ((phaseLowerPolynomial_hasDerivAt R x j).sub
        ((hasDerivAt_id x).const_mul L)).differentiableAt.differentiableWithinAt)
    intro x hx
    have hx' : x ∈ Set.Icc 0 R := interior_subset hx
    have hdf : HasDerivAt (fun x => P x-L*x)
        (phaseLowerPolynomialDeriv R j x-L) x := by
      convert (phaseLowerPolynomial_hasDerivAt R x j).sub
        ((hasDerivAt_id x).const_mul L) using 1 <;> first | rfl | ring
    rw [hdf.deriv]
    have hh := hdermono hx' (show R ∈ Set.Icc 0 R from ⟨hR, le_rfl⟩) hx'.2
    dsimp [L] at *
    linarith
  have hleftAnti : AntitoneOn left (Set.Iic R) := by
    have hneg {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) (hxy : x ≤ y) :
        left y ≤ left x := by
      dsimp [left]
      rw [max_eq_right hx, max_eq_right hy]
      nlinarith [mul_nonneg hL (sub_nonneg.mpr hxy)]
    have hpos {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ R) (hxy : x ≤ y) :
        left y ≤ left x := by
      have hh := hantiP ⟨hx, hxy.trans hy⟩ ⟨hx.trans hxy, hy⟩ hxy
      simpa only [left, max_eq_left hx, max_eq_left (hx.trans hxy)] using hh
    intro x hx y hy hxy
    by_cases hy0 : y ≤ 0
    · exact hneg (hxy.trans hy0) hy0 hxy
    · have hy0' : 0 ≤ y := le_of_lt (lt_of_not_ge hy0)
      by_cases hx0 : 0 ≤ x
      · exact hpos hx0 hy hxy
      · have hx0' : x ≤ 0 := le_of_lt (lt_of_not_ge hx0)
        exact (hpos le_rfl hy hy0').trans (hneg hx0' le_rfl hx0')
  have hc : 0 ≤ 1-κ := sub_nonneg.mpr hk.2.1
  have hrightConv : ConvexOn ℝ (Set.Ici R) right := by
    refine ⟨convex_Ici R, ?_⟩
    intro x hx y hy a b ha hb hab
    have hp := (convexOn_pow (j+10)).2 (hR.trans hx) (hR.trans hy) ha hb hab
    simp only [smul_eq_mul] at hp ⊢
    dsimp [right]
    nlinarith [mul_le_mul_of_nonneg_left hp hc]
  have hrightMono : MonotoneOn right (Set.Ici R) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici R)
      (show ContinuousOn right _ by dsimp [right]; fun_prop)
      (by dsimp [right]; fun_prop)
    intro x hx
    have hxR : R ≤ x := interior_subset hx
    have hxp := pow_le_pow_left₀ hR hxR (j+9)
    have hder : HasDerivAt right ((1-κ)*((j : ℝ)+10)*x^(j+9)-L) x := by
      convert ((hasDerivAt_pow (j+10) x).const_mul (1-κ)).sub
        ((hasDerivAt_id x).const_mul L) using 1
      · rfl
      · simp only [Nat.cast_add, Nat.cast_ofNat, show j+10-1=j+9 by omega]
        ring
    rw [hder.deriv]
    have hLP : L=(((j : ℝ)+2)-κ*((j : ℝ)+10))*R^(j+9) := by
      dsimp [L, phaseLowerPolynomialDeriv]
      rw [show j+9=8+(j+1) by omega, pow_add]
      ring
    rw [hLP]
    have hh := mul_le_mul_of_nonneg_left hxp
      (mul_nonneg hc (show 0 ≤ (j : ℝ)+10 by positivity))
    nlinarith [pow_nonneg hR (j+9)]
  have hmatch : left R=right R := by
    dsimp [left, right, P, phaseLowerPolynomial]
    rw [max_eq_left hR, show j+10=8+(j+2) by omega, pow_add]
    ring
  have hpiece := convexOn_univ_piecewise_Iic_of_antitoneOn_Iic_monotoneOn_Ici
    hleftConv hrightConv hleftAnti hrightMono hmatch
  have hlin : ConvexOn ℝ Set.univ (fun x : ℝ => L*x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul]
    exact le_of_eq (by ring)
  convert hlin.add hpiece using 1
  funext x
  by_cases hx : x ≤ R
  · have hx' : max x 0 ≤ R := max_le hx hR
    have hp : (max x 0)^(j+10) ≤ R^8*(max x 0)^(j+2) := by
      have hh := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (le_max_right x 0) hx' 8)
        (pow_nonneg (le_max_right x 0) (j+2))
      simpa only [show j+10=8+(j+2) by omega, pow_add] using hh
    simp [twoPowerPhaseTest, Set.piecewise, hx, max_eq_right hp,
      left, P, phaseLowerPolynomial]
  · have hx0 : 0 ≤ x := hR.trans (le_of_lt (lt_of_not_ge hx))
    have hp : R^8*x^(j+2) ≤ x^(j+10) := by
      have hh := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hR (le_of_lt (lt_of_not_ge hx)) 8)
        (pow_nonneg hx0 (j+2))
      simpa only [show j+10=8+(j+2) by omega, pow_add] using hh
    simp only [twoPowerPhaseTest, max_eq_left hx0, max_eq_left hp,
      Set.piecewise, Set.mem_Iic, if_neg hx, right, Pi.add_apply]
    ring

end
end SpringerLean

#print axioms SpringerLean.twoPowerPhaseTest_sub_power_convexOn
