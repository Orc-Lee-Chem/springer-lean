import SpringerLean.Round82FourierPair

namespace SpringerLean

open MeasureTheory
open scoped ComplexConjugate

/-- For a smooth periodic complex curve, twice the oriented Green
circulation is the imaginary part of its complex cross term. The
subsequent Fourier calculation can be performed on the complex term. -/
theorem oriented_boundary_twice_eq_complex_cross
    (γ : ℝ → ℂ)
    (hγ : Differentiable ℝ γ)
    (hder : Continuous (deriv γ))
    (hperiod : γ (2 * Real.pi) = γ 0) :
    2 * (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γ θ).re * deriv (fun t : ℝ => (γ t).im) θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (γ θ) * deriv γ θ).im := by
  let X : ℝ → ℝ := fun θ => (γ θ).re
  let Y : ℝ → ℝ := fun θ => (γ θ).im
  have hX : Differentiable ℝ X := by
    intro θ
    exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ
      (hγ θ).hasDerivAt).differentiableAt
  have hY : Differentiable ℝ Y := by
    intro θ
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
      (hγ θ).hasDerivAt).differentiableAt
  have hXd (θ : ℝ) : deriv X θ = (deriv γ θ).re := by
    simpa only [X, Function.comp_def, Complex.reCLM_apply] using
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ
        (hγ θ).hasDerivAt).deriv
  have hYd (θ : ℝ) : deriv Y θ = (deriv γ θ).im := by
    simpa only [Y, Function.comp_def, Complex.imCLM_apply] using
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
        (hγ θ).hasDerivAt).deriv
  have hXdcont : Continuous (deriv X) := by
    have heq : deriv X = fun θ => (deriv γ θ).re := funext hXd
    rw [heq]
    exact Complex.continuous_re.comp hder
  have hYdcont : Continuous (deriv Y) := by
    have heq : deriv Y = fun θ => (deriv γ θ).im := funext hYd
    rw [heq]
    exact Complex.continuous_im.comp hder
  have hprod : X (2 * Real.pi) * Y (2 * Real.pi) = X 0 * Y 0 := by
    simp only [X, Y, hperiod]
  have hskew := oriented_boundary_twice_eq_skew_integral
    X Y hX hY hXdcont hYdcont hprod
  convert hskew using 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp [X, Y]
  rw [hXd, hYd, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring


/-- At the standard `2π` period, differentiating each Fourier mode
multiplies its coefficient by `i` times its integer frequency. -/
theorem finiteFourierPolynomial_deriv_standard_period
    (s : Finset ℤ) (c : ℤ → ℂ) (θ : ℝ) :
    deriv (fun t : ℝ =>
      finiteFourierPolynomial (2 * Real.pi) s c
        (t : AddCircle (2 * Real.pi))) θ =
      Complex.I *
        finiteFourierPolynomial (2 * Real.pi) s
          (fun n => (n : ℂ) * c n)
          (θ : AddCircle (2 * Real.pi)) := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩
  have h := (finiteFourierPolynomial_hasDerivAt_real
    (2 * Real.pi) s c θ).deriv
  rw [h]
  unfold finiteFourierPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi).ne'
  push_cast
  field_simp [hπ]

/-- Conjugate-first weighted Fourier pairing, the orientation needed for
`Im (conj γ · γ′)`. -/
theorem finiteFourierPolynomial_weighted_cross_interval
    (T : ℝ) [Fact (0 < T)] (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ t in (0 : ℝ)..T,
      conj (finiteFourierPolynomial T s c (t : AddCircle T)) *
        finiteFourierPolynomial T s
          (fun n => (n : ℂ) * c n) (t : AddCircle T)) =
      (T : ℂ) * ∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
  have hswap :
      (∫ t in (0 : ℝ)..T,
        conj (finiteFourierPolynomial T s c (t : AddCircle T)) *
          finiteFourierPolynomial T s
            (fun n => (n : ℂ) * c n) (t : AddCircle T)) =
      (∫ t in (0 : ℝ)..T,
        finiteFourierPolynomial T s
          (fun n => (n : ℂ) * c n) (t : AddCircle T) *
          star (finiteFourierPolynomial T s c (t : AddCircle T))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    change conj _ * _ = _ * conj _
    ring
  rw [hswap, finiteFourierPolynomial_pairing_interval]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  change ((n : ℂ) * c n) * conj (c n) = _
  rw [mul_assoc, Complex.mul_conj']
  push_cast
  rfl

/-- Exact finite signed Green/Fourier identity. The frequency sign is
retained, so negative Laurent modes subtract from the area. -/
theorem finiteFourierPolynomial_oriented_boundary_twice
    (s : Finset ℤ) (c : ℤ → ℂ) :
    2 * (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (finiteFourierPolynomial (2 * Real.pi) s c
        (θ : AddCircle (2 * Real.pi))).re *
      deriv (fun t : ℝ =>
        (finiteFourierPolynomial (2 * Real.pi) s c
          (t : AddCircle (2 * Real.pi))).im) θ) =
      (((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ)).re := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩
  let γ : ℝ → ℂ := fun θ =>
    finiteFourierPolynomial (2 * Real.pi) s c
      (θ : AddCircle (2 * Real.pi))
  let W : ℝ → ℂ := fun θ =>
    finiteFourierPolynomial (2 * Real.pi) s
      (fun n => (n : ℂ) * c n)
      (θ : AddCircle (2 * Real.pi))
  have hγ : Differentiable ℝ γ := by
    intro θ
    exact (finiteFourierPolynomial_hasDerivAt_real
      (2 * Real.pi) s c θ).differentiableAt
  have hγcont : Continuous γ := hγ.continuous
  have hWcont : Continuous W := by
    dsimp [W, finiteFourierPolynomial]
    fun_prop
  have hγder (θ : ℝ) : deriv γ θ = Complex.I * W θ :=
    finiteFourierPolynomial_deriv_standard_period s c θ
  have hdercont : Continuous (deriv γ) := by
    have heq : deriv γ = fun θ => Complex.I * W θ := funext hγder
    rw [heq]
    exact continuous_const.mul hWcont
  have hperiod : γ (2 * Real.pi) = γ 0 := by
    have hp : (((0 : ℝ) + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi)) =
        ((0 : ℝ) : AddCircle (2 * Real.pi)) :=
      AddCircle.coe_add_period (2 * Real.pi) 0
    dsimp [γ]
    simpa using congrArg
      (finiteFourierPolynomial (2 * Real.pi) s c) hp
  have hInt : IntervalIntegrable
      (fun θ : ℝ => conj (γ θ) * W θ)
      volume 0 (2 * Real.pi) :=
    ((Complex.continuous_conj.comp hγcont).mul hWcont).intervalIntegrable
      0 (2 * Real.pi)
  have hpoint :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (γ θ) * deriv γ θ).im) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (γ θ) * W θ).re := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change (conj (γ θ) * deriv γ θ).im = (conj (γ θ) * W θ).re
    rw [hγder]
    have heq : conj (γ θ) * (Complex.I * W θ) =
        Complex.I * (conj (γ θ) * W θ) := by ring
    rw [heq]
    simp [Complex.mul_im]
  have hFourier :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        conj (γ θ) * W θ) =
        ((2 * Real.pi : ℝ) : ℂ) *
          ∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ) :=
    finiteFourierPolynomial_weighted_cross_interval
      (2 * Real.pi) s c
  change 2 * (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (γ θ).re * deriv (fun t : ℝ => (γ t).im) θ) = _
  calc
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (γ θ) * deriv γ θ).im :=
      oriented_boundary_twice_eq_complex_cross γ hγ hdercont hperiod
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (conj (γ θ) * W θ).re := hpoint
    _ = (∫ θ in (0 : ℝ)..(2 * Real.pi),
        conj (γ θ) * W θ).re := intervalIntegral.intervalIntegral_re hInt
    _ = _ := by rw [hFourier]

/-- Exact finite signed boundary area on the ordinary real angle interval.
The positive and negative frequencies enter with their integer signs. -/
theorem finiteFourierPolynomial_oriented_boundary
    (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (finiteFourierPolynomial (2 * Real.pi) s c
        (θ : AddCircle (2 * Real.pi))).re *
      deriv (fun t : ℝ =>
        (finiteFourierPolynomial (2 * Real.pi) s c
          (t : AddCircle (2 * Real.pi))).im) θ) =
      Real.pi * ∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2 := by
  have h := finiteFourierPolynomial_oriented_boundary_twice s c
  have hsum :
      (∑ n ∈ s, (n : ℂ) * ((‖c n‖ ^ 2 : ℝ) : ℂ)) =
        ((∑ n ∈ s, (n : ℝ) * ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hsum] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at h
  linarith
end SpringerLean