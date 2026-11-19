import SpringerLean.Round1924ActualContinuousMoment

open scoped ComplexConjugate

namespace SpringerLean

noncomputable def oddStarSeed (t : ℝ) (z : ℂ) : ℂ :=
  let s := Real.sqrt (1 - t ^ 2)
  (z - (t : ℂ) * Complex.I + s) ^ 2 /
    (z - (t : ℂ) * Complex.I)

/-- The Möbius partner of a point outside the circle is inside it for
every real perturbation parameter |t|<1. -/
theorem oddStarSeed_partner_norm_identity (t : ℝ) (z : ℂ) :
    ‖z - (t : ℂ) * Complex.I‖ ^ 2 -
      ‖1 + (t : ℂ) * Complex.I * z‖ ^ 2 =
        (1 - t ^ 2) * (‖z‖ ^ 2 - 1) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  ring

/-- The seed map used for each odd-star counterexample is injective on the
open exterior disk. The remaining factor-constant variation is separate. -/
theorem oddStarSeed_injOn_exteriorDisk
    (t : ℝ) (ht : |t| < 1) :
    Set.InjOn (oddStarSeed t) exteriorDisk := by
  intro z hz w hw heq
  change 1 < ‖z‖ at hz
  change 1 < ‖w‖ at hw
  let s : ℝ := Real.sqrt (1 - t ^ 2)
  let u : ℂ := z - (t : ℂ) * Complex.I
  let v : ℂ := w - (t : ℂ) * Complex.I
  have hu : u ≠ 0 := by
    intro h
    have hz' : z = (t : ℂ) * Complex.I := sub_eq_zero.mp h
    have hn : ‖z‖ = |t| := by
      rw [hz', norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rfl
    rw [hn] at hz
    linarith
  have hv : v ≠ 0 := by
    intro h
    have hw' : w = (t : ℂ) * Complex.I := sub_eq_zero.mp h
    have hn : ‖w‖ = |t| := by
      rw [hw', norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
      rfl
    rw [hn] at hw
    linarith
  change (u + (s : ℂ)) ^ 2 / u = (v + (s : ℂ)) ^ 2 / v at heq
  have heq' := (div_eq_div_iff hu hv).mp heq
  have hfactor :
      ((u + (s : ℂ)) ^ 2 * v - (v + (s : ℂ)) ^ 2 * u) =
        (u - v) * (u * v - (s : ℂ) ^ 2) := by ring
  have hprod : (u - v) * (u * v - (s : ℂ) ^ 2) = 0 := by
    rw [← hfactor, sub_eq_zero]
    exact heq'
  rcases mul_eq_zero.mp hprod with hsame | hpartner
  · have huv : u = v := sub_eq_zero.mp hsame
    dsimp [u, v] at huv
    calc
      z = (z - (t : ℂ) * Complex.I) + (t : ℂ) * Complex.I := by ring
      _ = (w - (t : ℂ) * Complex.I) + (t : ℂ) * Complex.I := by rw [huv]
      _ = w := by ring
  · have htsq : 0 ≤ 1 - t ^ 2 := by
      rcases abs_lt.mp ht with ⟨htlow, hthi⟩
      nlinarith
    have hs2 : (s : ℂ) ^ 2 = (1 - t ^ 2 : ℝ) := by
      exact_mod_cast Real.sq_sqrt htsq
    have hp : u * v = (s : ℂ) ^ 2 := sub_eq_zero.mp hpartner
    have hwformula : w = (1 + (t : ℂ) * Complex.I * z) / u := by
      apply (eq_div_iff hu).mpr
      have hwv : w = v + (t : ℂ) * Complex.I := by dsimp [v]; ring
      rw [hwv]
      calc
        (v + (t : ℂ) * Complex.I) * u =
            u * v + (t : ℂ) * Complex.I * u := by ring
        _ = 1 + (t : ℂ) * Complex.I * z := by
          rw [hp, hs2]
          dsimp [u]
          push_cast
          ring_nf
          simp [Complex.I_sq]
    have hq : 0 < 1 - t ^ 2 := by
      rcases abs_lt.mp ht with ⟨htlow, hthi⟩
      nlinarith
    have hz2 : 0 < ‖z‖ ^ 2 - 1 := by
      have hz1 : 1 < ‖z‖ := hz
      nlinarith [norm_nonneg z]
    have hdiff := oddStarSeed_partner_norm_identity t z
    have hpos := mul_pos hq hz2
    have hnum : ‖1 + (t : ℂ) * Complex.I * z‖ < ‖u‖ := by
      dsimp [u]
      nlinarith [norm_nonneg (1 + (t : ℂ) * Complex.I * z),
        norm_nonneg (z - (t : ℂ) * Complex.I)]
    have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hwsmall : ‖w‖ < 1 := by
      rw [hwformula, norm_div]
      exact (div_lt_one hu0).mpr hnum
    exact False.elim ((not_lt_of_ge (le_of_lt hw)) hwsmall)

end SpringerLean

#print axioms SpringerLean.oddStarSeed_partner_norm_identity
#print axioms SpringerLean.oddStarSeed_injOn_exteriorDisk
