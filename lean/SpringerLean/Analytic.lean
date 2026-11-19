import SpringerLean.Slit
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

namespace SpringerLean

/-- The slit map is analytic at every point of the actual exterior domain. -/
theorem slitMap_analyticAt (a z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (slitMap a) z := by
  unfold slitMap
  fun_prop


/-- The complex derivative of the Joukowski map. -/
theorem slitMap_hasDerivAt (a z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (slitMap a) (1 - a / z ^ 2) z := by
  have hinv : HasDerivAt (fun y : ℂ => y⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz
  have h := HasDerivAt.add (hasDerivAt_id z) (HasDerivAt.const_mul a hinv)
  have hder : 1 + a * (-(z ^ 2)⁻¹) = 1 - a / z ^ 2 := by
    field_simp [hz]
    ring
  have hfun : (id + fun y : ℂ => a * y⁻¹) = slitMap a := by
    funext y
    simp [slitMap, div_eq_mul_inv]
  rw [hfun] at h
  rw [hder] at h
  exact h

/-- The derivative cannot vanish in the open exterior disk when `|a|=1`. -/
theorem slitMap_deriv_ne_zero (a z : ℂ) (ha : ‖a‖ = 1)
    (hz : z ∈ exteriorDisk) : deriv (slitMap a) z ≠ 0 := by
  have hz0 : z ≠ 0 := exterior_ne_zero hz
  rw [(slitMap_hasDerivAt a z hz0).deriv]
  intro h
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have hdiv : a / z ^ 2 = 1 := (sub_eq_zero.mp h).symm
  have heq : a = z ^ 2 := by
    apply (div_eq_iff hz2).mp hdiv |>.trans
    simp
  have hnorm : ‖z‖ ^ 2 = 1 := by
    rw [← norm_pow, ← heq, ha]
  have hz1 : 1 < ‖z‖ := hz
  nlinarith

/-- A genuine analytic local inverse exists at every point of the slit-map image. -/
theorem slitMap_analytic_local_inverse (a z : ℂ) (ha : ‖a‖ = 1)
    (hz : z ∈ exteriorDisk) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (slitMap a z) ∧
      g (slitMap a z) = z ∧
      (∀ᶠ w in nhds (slitMap a z), slitMap a (g w) = w) := by
  have hz0 : z ≠ 0 := exterior_ne_zero hz
  let hf := slitMap_analyticAt a z hz0
  let hd := slitMap_deriv_ne_zero a z ha hz
  let g := hf.hasStrictDerivAt.localInverse _ _ _ hd
  refine ⟨g, hf.analyticAt_localInverse hd, ?_, ?_⟩
  · exact HasStrictFDerivAt.localInverse_apply_image ..
  · exact hf.hasStrictDerivAt.eventually_right_inverse hd

/-- The actual inverse on the image, extended arbitrarily outside the image. -/
noncomputable def slitInverse (a : ℂ) : ℂ → ℂ :=
  Function.invFunOn (slitMap a) exteriorDisk

theorem slitInverse_apply (a z : ℂ) (ha : ‖a‖ = 1)
    (hz : z ∈ exteriorDisk) : slitInverse a (slitMap a z) = z := by
  exact (slitMap_injOn a ha).leftInvOn_invFunOn hz

theorem exteriorDisk_isOpen : IsOpen exteriorDisk := by
  change IsOpen {z : ℂ | (1 : ℝ) < ‖z‖}
  exact isOpen_lt continuous_const continuous_norm

/-- The actual inverse is analytic at every image point. -/
theorem slitInverse_analyticAt (a : ℂ) (ha : ‖a‖ = 1) (w : ℂ)
    (hw : w ∈ slitMap a '' exteriorDisk) :
    AnalyticAt ℂ (slitInverse a) w := by
  rcases hw with ⟨z, hz, rfl⟩
  rcases slitMap_analytic_local_inverse a z ha hz with ⟨g, hg, hgz, hright⟩
  have hcenter : g (slitMap a z) ∈ exteriorDisk := by rw [hgz]; exact hz
  have hmem : ∀ᶠ y in nhds (slitMap a z), g y ∈ exteriorDisk :=
    hg.continuousAt.eventually (exteriorDisk_isOpen.mem_nhds hcenter)
  apply hg.congr
  filter_upwards [hmem, hright] with y hgy hJ
  have hy : y ∈ slitMap a '' exteriorDisk := ⟨g y, hgy, hJ⟩
  have hi : slitMap a (slitInverse a y) = y := Function.invFunOn_eq hy
  have hmi : slitInverse a y ∈ exteriorDisk := Function.invFunOn_mem hy
  exact (slitMap_injOn a ha) hgy hmi (hJ.trans hi.symm)

/-- The actual analytic inverse satisfies the quadratic equation on the image. -/
theorem slitInverse_quadratic (a w : ℂ)
    (hw : w ∈ slitMap a '' exteriorDisk) :
    slitInverse a w * slitInverse a w - w * slitInverse a w + a = 0 := by
  have hpre := Function.invFunOn_pos hw
  exact (slitMap_eq_iff_quadratic a (slitInverse a w) w
    (exterior_ne_zero hpre.1)).mp hpre.2

/-- Exact first-order error along the actual inverse branch at exterior points. -/
theorem slitInverse_firstCoeff_error (a z : ℂ) (ha : ‖a‖ = 1)
    (hz : z ∈ exteriorDisk) :
    slitMap a z * (slitMap a z - slitInverse a (slitMap a z)) - a =
      a ^ 2 / z ^ 2 := by
  rw [slitInverse_apply a z ha hz]
  have hz0 : z ≠ 0 := exterior_ne_zero hz
  dsimp [slitMap]
  field_simp [hz0]
  ring

/-- Quantitative decay of the first-coefficient error on the actual image. -/
theorem slitInverse_firstCoeff_error_norm (a z : ℂ) (ha : ‖a‖ = 1)
    (hz : z ∈ exteriorDisk) :
    ‖slitMap a z * (slitMap a z - slitInverse a (slitMap a z)) - a‖ =
      1 / ‖z‖ ^ 2 := by
  rw [slitInverse_firstCoeff_error a z ha hz, norm_div, norm_pow, norm_pow, ha]
  ring
end SpringerLean