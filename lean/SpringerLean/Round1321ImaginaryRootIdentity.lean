import SpringerLean.Round1320OddKernel25
import SpringerLean.Round457OmittedSquareRootLift
import SpringerLean.Round08General

namespace SpringerLean
set_option Elab.async false
open scoped ComplexConjugate

/-- The two-line imaginary-point calculation, stated for the actual
odd square root of an actual exterior map.  This is an identity before
any use of the tail or area estimates. -/
theorem actualHarmonic_neg24_25_odd_root_identity
    (F H : ℂ → ℂ) (R : ℝ)
    (hsquare : ∀ z ∈ exteriorDisk, H z ^ 2 = F (z ^ 2) - (R : ℂ)) :
    let r : ℝ := largeRootRadius
    let A : ℂ := (R : ℂ)/2
    let M : ℂ := (r : ℂ)+A/(r : ℂ)
    let T : ℂ := H (Complex.I*(r : ℂ))-Complex.I*M
    actualHarmonic F (-(24/25 : ℂ)) =
      -(1+A^2)*(24/25 : ℂ)+2*Complex.I*M*T+T^2 := by
  dsimp only
  let r : ℝ := largeRootRadius
  let A : ℂ := (R : ℂ)/2
  let M : ℂ := (r : ℂ)+A/(r : ℂ)
  let T : ℂ := H (Complex.I*(r : ℂ))-Complex.I*M
  change actualHarmonic F (-(24/25 : ℂ)) =
    -(1+A^2)*(24/25 : ℂ)+2*Complex.I*M*T+T^2
  have hr : 1 < r := largeRootRadius_gt_one
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one hr))
  have hr2 : (r : ℂ)^2 = (25/24 : ℂ) := by
    have hs : r^2 = (25/24 : ℝ) := largeRootRadius_sq
    have hh := congrArg (fun x : ℝ => (x : ℂ)) hs
    norm_num at hh
    exact hh
  have hz : Complex.I*(r : ℂ) ∈ exteriorDisk := by
    change 1 < ‖Complex.I*(r : ℂ)‖
    simpa [norm_mul, Complex.norm_real, abs_of_pos (lt_trans zero_lt_one hr)] using hr
  have hzsq : (Complex.I*(r : ℂ))^2 = -(25/24 : ℂ) := by
    rw [mul_pow, Complex.I_sq, hr2]
    ring
  have hs := hsquare _ hz
  rw [hzsq] at hs
  have hH : H (Complex.I*(r : ℂ)) = Complex.I*M+T := by
    dsimp [T]
    ring
  rw [hH] at hs
  have hF : F (-(25/24 : ℂ)) = (R : ℂ)+(Complex.I*M+T)^2 := by
    linear_combination -hs
  have hfill : actualHarmonic F (-(24/25 : ℂ)) =
      F (-(25/24 : ℂ))+(25/24 : ℂ)-(24/25 : ℂ) := by
    have hu : (-(24/25 : ℂ)) ≠ 0 := by norm_num
    have hinv : (-(24/25 : ℂ))⁻¹ = -(25/24 : ℂ) := by norm_num
    have hconj : conj (-(24/25 : ℂ)) = -(24/25 : ℂ) := by
      have hcast : (-(24/25 : ℂ)) = ((-(24/25 : ℝ)) : ℂ) := by norm_num
      rw [hcast]
      simpa only [map_neg] using
        congrArg Neg.neg (Complex.conj_ofReal (24/25 : ℝ))
    rw [actualHarmonic, hconj, exteriorForwardGerm_punctured F hu, hinv]
    ring
  rw [hfill, hF]
  have hqinv : (24/25 : ℂ) = ((r : ℂ)^2)⁻¹ := by
    rw [hr2]
    norm_num
  rw [← hr2, hqinv]
  dsimp [M, A]
  field_simp [hr0]
  ring_nf
  simp [Complex.I_sq]
  ring

end SpringerLean
