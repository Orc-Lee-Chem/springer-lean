import Mathlib.Analysis.Complex.Schwarz

open Set Metric
open scoped ComplexConjugate

namespace SpringerLean

/-- A disk automorphism carrying its parameter to zero. -/
noncomputable def diskMobius (a z : ℂ) : ℂ := (z-a)/(1-conj a*z)

private theorem diskMobius_norm_square_identity (a z : ℂ) :
    ‖1-conj a*z‖^2 - ‖z-a‖^2 = (1-‖a‖^2)*(1-‖z‖^2) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

private theorem diskMobius_norm_lt
    {a z : ℂ} (ha : a ∈ ball (0:ℂ) 1) (hz : z ∈ ball (0:ℂ) 1) :
    ‖z-a‖ < ‖1-conj a*z‖ := by
  have ha' := mem_ball_zero_iff.mp ha
  have hz' := mem_ball_zero_iff.mp hz
  have haPos : 0 < 1-‖a‖^2 := by nlinarith [norm_nonneg a]
  have hzPos : 0 < 1-‖z‖^2 := by nlinarith [norm_nonneg z]
  have h := diskMobius_norm_square_identity a z
  have hpos := mul_pos haPos hzPos
  nlinarith [norm_nonneg (z-a),norm_nonneg (1-conj a*z)]

theorem diskMobius_den_ne_zero
    {a z : ℂ} (ha : a ∈ ball (0:ℂ) 1) (hz : z ∈ ball (0:ℂ) 1) :
    1-conj a*z ≠ 0 :=
  norm_pos_iff.mp ((norm_nonneg _).trans_lt (diskMobius_norm_lt ha hz))

theorem diskMobius_mapsTo {a : ℂ} (ha : a ∈ ball (0:ℂ) 1) :
    MapsTo (diskMobius a) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff,diskMobius,norm_div]
  exact (div_lt_one₀ (norm_pos_iff.mpr (diskMobius_den_ne_zero ha hz))).mpr (diskMobius_norm_lt ha hz)

theorem diskMobius_differentiableOn {a : ℂ} (ha : a ∈ ball (0:ℂ) 1) :
    DifferentiableOn ℂ (diskMobius a) (ball 0 1) := by
  unfold diskMobius
  exact (differentiable_id.sub_const a).differentiableOn.div
    (show Differentiable ℂ (fun z => 1-conj a*z) by fun_prop).differentiableOn
    (fun _ hz => diskMobius_den_ne_zero ha hz)

theorem diskMobius_at_parameter (a : ℂ) : diskMobius a a = 0 := by simp [diskMobius]

theorem diskMobius_at_zero (a : ℂ) : diskMobius a 0 = -a := by simp [diskMobius]

theorem neg_mem_unitDisk {a : ℂ} (ha : a ∈ ball (0:ℂ) 1) : -a ∈ ball (0:ℂ) 1 := by
  simpa only [mem_ball_zero_iff,norm_neg] using ha

theorem diskMobius_leftInverse
    {a z : ℂ} (ha : a ∈ ball (0:ℂ) 1) (hz : z ∈ ball (0:ℂ) 1) :
    diskMobius (-a) (diskMobius a z) = z := by
  have hden := diskMobius_den_ne_zero ha hz
  have hin := diskMobius_den_ne_zero (neg_mem_unitDisk ha) (diskMobius_mapsTo ha hz)
  change (diskMobius a z - (-a))/(1-conj (-a)*diskMobius a z) = z
  apply (div_eq_iff hin).mpr
  rw [map_neg]
  let d := 1-conj a*z
  change (z-a)/d - (-a) = z*(1-(-conj a)*((z-a)/d))
  have hd : d ≠ 0 := hden
  have hmul : d*((z-a)/d) = z-a := by field_simp [hd]
  apply mul_left_cancel₀ hd
  calc
    d*((z-a)/d - (-a)) = z-a+d*a := by rw [mul_sub,hmul]; ring
    _ = z*(d-(-conj a)*(z-a)) := by dsimp [d]; ring
    _ = d*(z*(1-(-conj a)*((z-a)/d))) := by
      rw [mul_left_comm d z]
      congr 1
      conv_rhs => rw [mul_sub,mul_one,mul_left_comm d (-conj a),hmul]

theorem diskMobius_injOn {a : ℂ} (ha : a ∈ ball (0:ℂ) 1) :
    InjOn (diskMobius a) (ball 0 1) := by
  intro z hz w hw he
  exact (diskMobius_leftInverse ha hz).symm.trans
    ((congrArg (diskMobius (-a)) he).trans (diskMobius_leftInverse ha hw))

end SpringerLean
