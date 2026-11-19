import SpringerLean.Round1424AffineAngleMap

open Filter

namespace SpringerLean
set_option maxHeartbeats 200000

theorem refinedAffine_angle_differentiableAt
    {γ φ : ℝ} (hγ : 0 < γ)
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ Real.pi/2)
    (hshort : 2-2*Real.cos φ ≤ γ*(51/500:ℝ)) :
    DifferentiableAt ℝ (refinedAffineAngle γ) φ := by
  obtain ⟨hq0,hq1⟩ :=
    refinedAffine_angle_argument_range hγ hφ0 hφ hshort
  have harg : DifferentiableAt ℝ
      (fun w : ℝ => Real.sin (w/2)/Real.sqrt γ) φ := by
    fun_prop (disch := positivity)
  unfold refinedAffineAngle
  exact ((Real.differentiableAt_arcsin.2
    ⟨by linarith, by linarith⟩).comp φ harg).const_mul 2

/-- The derivative identity is obtained by differentiating the exact
projection-deficit relation on an open short arc. -/
theorem refinedAffine_angle_deriv_identity
    {γ φ : ℝ} (hγ : 0 < γ)
    (hφ0 : 0 < φ) (hφ : φ < Real.pi/2)
    (hshort : 2-2*Real.cos φ < γ*(51/500:ℝ)) :
    γ*Real.sin (refinedAffineAngle γ φ)*
      deriv (refinedAffineAngle γ) φ = Real.sin φ := by
  have hdiff := refinedAffine_angle_differentiableAt hγ hφ0.le hφ.le hshort.le
  have hcont : ContinuousAt (fun w : ℝ => 2-2*Real.cos w) φ := by fun_prop
  have hshortEv : ∀ᶠ w in nhds φ,
      2-2*Real.cos w < γ*(51/500:ℝ) :=
    hcont.eventually (isOpen_Iio.mem_nhds hshort)
  have hlocal : ∀ᶠ w in nhds φ,
      γ*(2-2*Real.cos (refinedAffineAngle γ w)) =
        2-2*Real.cos w := by
    filter_upwards [Ioo_mem_nhds hφ0 hφ,hshortEv] with w hw hwshort
    exact refinedAffine_angle_deficit hγ hw.1.le hw.2.le hwshort.le
  have hleft : HasDerivAt
      (fun w : ℝ => γ*(2-2*Real.cos (refinedAffineAngle γ w)))
      (γ*2*Real.sin (refinedAffineAngle γ φ)*
        deriv (refinedAffineAngle γ) φ) φ := by
    have hbase := ((Real.hasDerivAt_cos (refinedAffineAngle γ φ)).comp
      φ hdiff.hasDerivAt).const_mul (-2) |>.const_add 2 |>.const_mul γ
    convert hbase using 1
    · funext x; dsimp; ring
    · ring
  have hright : HasDerivAt (fun w : ℝ => 2-2*Real.cos w)
      (2*Real.sin φ) φ := by
    convert (Real.hasDerivAt_cos φ).const_mul (-2) |>.const_add 2 using 1 <;> ring
  have heq := hleft.congr_of_eventuallyEq (by
    filter_upwards [hlocal] with w hw
    exact hw.symm)
  have hder := heq.unique hright
  nlinarith

/-- Exact derivative of the inverse angular map. The deficit `s`
belongs to the original test angle `θ`, not the model angle `φ`. -/
theorem refinedAffine_angle_deriv_formula
    {γ φ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hφ0 : 0 < φ) (hφ : φ < Real.pi/2)
    (hshort : 2-2*Real.cos φ < γ*(51/500:ℝ)) :
    let θ := refinedAffineAngle γ φ
    let s := 2-2*Real.cos θ
    deriv (refinedAffineAngle γ) φ =
      Real.sqrt ((4-γ*s)/(4-s))/Real.sqrt γ := by
  dsimp
  let θ : ℝ := refinedAffineAngle γ φ
  let s : ℝ := 2-2*Real.cos θ
  let D : ℝ := deriv (refinedAffineAngle γ) φ
  have hθrange := refinedAffine_angle_range hγ hφ0.le hφ.le hshort.le
  have hθdef := refinedAffine_angle_deficit hγ hφ0.le hφ.le hshort.le
  change γ*s=2-2*Real.cos φ at hθdef
  have hqPos : 0 < Real.sin (φ/2)/Real.sqrt γ := by
    apply div_pos
    · exact Real.sin_pos_of_pos_of_lt_pi (by linarith)
        (by linarith [Real.pi_pos])
    · exact Real.sqrt_pos.2 hγ
  have hqLt : Real.sin (φ/2)/Real.sqrt γ < 1 := by
    have hh := refinedAffine_angle_argument_range hγ hφ0.le hφ.le hshort.le
    linarith [hh.2]
  have hθ0 : 0 < θ := by
    dsimp [θ,refinedAffineAngle]
    exact mul_pos (by norm_num) (Real.arcsin_pos.2 hqPos)
  have hθpi : θ < Real.pi := by
    dsimp [θ,refinedAffineAngle]
    linarith [Real.arcsin_lt_pi_div_two.2 hqLt]
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hsinφ : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ0 (by linarith [Real.pi_pos])
  have hid := refinedAffine_angle_deriv_identity hγ hφ0 hφ hshort
  change γ*Real.sin θ*D = Real.sin φ at hid
  have hD0 : 0 < D := by
    have hprod : 0 < (γ*Real.sin θ)*D := by
      nlinarith [hid,hsinφ]
    exact (mul_pos_iff_of_pos_left (mul_pos hγ hsinθ)).mp hprod
  have hs0 : 0 < s := by
    have htrig := Real.sin_sq_add_cos_sq θ
    dsimp [s]
    nlinarith [sq_pos_of_pos hsinθ]
  have hsupper : s < 51/500 := by
    nlinarith [hθdef]
  have hs4 : 0 < 4-s := by linarith
  have hnum : 0 < 4-γ*s := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) hs0.le]
  have hsinsq (x : ℝ) :
      Real.sin x ^ 2 =
        (2-2*Real.cos x)*(4-(2-2*Real.cos x))/4 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hθsinSq : Real.sin θ^2=s*(4-s)/4 := by
    simpa [s] using hsinsq θ
  have hφsinSq : Real.sin φ^2=γ*s*(4-γ*s)/4 := by
    rw [hsinsq φ, ← hθdef]
  have hidSq := congrArg (fun x : ℝ => x^2) hid
  have hfactor : (γ*s)*(γ*(4-s)*D^2) =
      (γ*s)*(4-γ*s) := by
    rw [mul_pow,mul_pow,hθsinSq,hφsinSq] at hidSq
    nlinarith [hidSq]
  have hcancel : γ*(4-s)*D^2=4-γ*s := by
    exact (mul_left_cancel₀ (ne_of_gt (mul_pos hγ hs0)) hfactor)
  have hDsq : D^2=(4-γ*s)/(γ*(4-s)) := by
    apply (eq_div_iff (ne_of_gt (mul_pos hγ hs4))).2
    nlinarith [hcancel]
  have hrootPos : 0 ≤
      Real.sqrt ((4-γ*s)/(4-s))/Real.sqrt γ := by positivity
  have hrootSq :
      (Real.sqrt ((4-γ*s)/(4-s))/Real.sqrt γ)^2 =
      (4-γ*s)/(γ*(4-s)) := by
    rw [div_pow,Real.sq_sqrt (div_nonneg hnum.le hs4.le),
      Real.sq_sqrt hγ.le]
    field_simp [ne_of_gt hγ, ne_of_gt hs4,
      ne_of_gt (mul_pos hγ hs4)]
  change D = _
  nlinarith

end SpringerLean

#print axioms SpringerLean.refinedAffine_angle_differentiableAt
#print axioms SpringerLean.refinedAffine_angle_deriv_identity
#print axioms SpringerLean.refinedAffine_angle_deriv_formula
