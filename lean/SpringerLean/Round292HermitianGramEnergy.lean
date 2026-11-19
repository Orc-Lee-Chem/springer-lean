import SpringerLean.Round291UniversalGrunsky
import Mathlib.Algebra.MvPolynomial.Rename

namespace SpringerLean

abbrev RationalHermitianPolynomial := MvPolynomial (Bool × ℕ) ℚ

noncomputable def actualHermitianPolynomialEval (F : ℂ → ℂ) :
    RationalHermitianPolynomial →+* ℂ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ℂ)
    (fun v => if v.1 then star (exteriorForwardCoeff F v.2) else exteriorForwardCoeff F v.2)

noncomputable def rationalHermitianNormSq (p : MvPolynomial ℕ ℚ) : RationalHermitianPolynomial :=
  MvPolynomial.rename (fun i => (false, i)) p *
    MvPolynomial.rename (fun i => (true, i)) p

theorem actualHermitianPolynomialEval_holomorphic
    (F : ℂ → ℂ) (p : MvPolynomial ℕ ℚ) :
    actualHermitianPolynomialEval F (MvPolynomial.rename (fun i => (false, i)) p) =
      actualForwardPolynomialEval F p := by
  have hh : (actualHermitianPolynomialEval F).comp
      (MvPolynomial.rename (fun i => (false, i))).toRingHom = actualForwardPolynomialEval F := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [actualHermitianPolynomialEval, actualForwardPolynomialEval,
        MvPolynomial.rename_C]
    · intro i
      simp [actualHermitianPolynomialEval, actualForwardPolynomialEval]
  exact RingHom.congr_fun hh p

theorem actualHermitianPolynomialEval_antiholomorphic
    (F : ℂ → ℂ) (p : MvPolynomial ℕ ℚ) :
    actualHermitianPolynomialEval F (MvPolynomial.rename (fun i => (true, i)) p) =
      star (actualForwardPolynomialEval F p) := by
  have hh : (actualHermitianPolynomialEval F).comp
      (MvPolynomial.rename (fun i => (true, i))).toRingHom =
        (starRingEnd ℂ).comp (actualForwardPolynomialEval F) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [actualHermitianPolynomialEval, actualForwardPolynomialEval,
        MvPolynomial.rename_C]
    · intro i
      simp [actualHermitianPolynomialEval, actualForwardPolynomialEval]
  exact RingHom.congr_fun hh p

theorem rationalHermitianNormSq_eval
    (F : ℂ → ℂ) (p : MvPolynomial ℕ ℚ) :
    actualHermitianPolynomialEval F (rationalHermitianNormSq p) =
      ((‖actualForwardPolynomialEval F p‖ ^ 2 : ℝ) : ℂ) := by
  rw [rationalHermitianNormSq, map_mul, actualHermitianPolynomialEval_holomorphic,
    actualHermitianPolynomialEval_antiholomorphic]
  simpa only [Complex.ofReal_pow, starRingEnd_apply] using
    Complex.mul_conj' (actualForwardPolynomialEval F p)

/-- The rational polynomial whose evaluation is the actual Schober
comparison diagonal. It is defined independently of any certificate. -/
noncomputable def universalSchoberDiagonal (k : ℕ) : RationalHermitianPolynomial :=
  ∑ j ∈ Finset.range k,
    MvPolynomial.C ((((j + 1 : ℕ) : ℚ) / (k : ℚ)) ^ 2) *
      rationalHermitianNormSq (universalPhiPowerCoeff k (k - 1 - j))

theorem universalSchoberDiagonal_eval
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (n : ℕ) :
    actualHermitianPolynomialEval F (universalSchoberDiagonal (n + 1)) =
      ((schoberActualDiagonal F (n + 1) : ℝ) : ℂ) := by
  rw [universalSchoberDiagonal, map_sum, schoberActualDiagonal_forward_formula F hc n]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, rationalHermitianNormSq_eval, universalPhiPowerCoeff_eval]
  simp only [actualHermitianPolynomialEval, MvPolynomial.eval₂Hom_C,
    Nat.add_sub_cancel, map_pow, map_div₀, map_natCast]
  push_cast
  rfl

end SpringerLean
