import SpringerLean.Round1373JacobianIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

namespace SpringerLean

noncomputable def coarseAngleDeficit (v : ℝ) : ℝ :=
  2-2*Real.cos v

noncomputable def coarseAngleBeta : ℝ := Real.arccos (39/40 : ℝ)
noncomputable def coarseAngleAlpha : ℝ := Real.arccos (31/32 : ℝ)

noncomputable def coarseAngleArgument (v : ℝ) : ℝ :=
  Real.sin (v/2)*Real.sqrt (1+5*coarseAngleDeficit v)

noncomputable def coarseAnglePhi (v : ℝ) : ℝ :=
  2*Real.arcsin (coarseAngleArgument v)

theorem coarseAngleBeta_range :
    0 ≤ coarseAngleBeta ∧ coarseAngleBeta ≤ Real.pi/2 := by
  constructor
  · exact Real.arccos_nonneg _
  · unfold coarseAngleBeta
    have h := Real.arccos_le_arccos (by norm_num : (0:ℝ) ≤ 39/40)
    simpa using h

theorem coarseAngleDeficit_range
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    0 ≤ coarseAngleDeficit v ∧ coarseAngleDeficit v ≤ 1/20 := by
  have hβπ : coarseAngleBeta ≤ Real.pi := by
    linarith [coarseAngleBeta_range.2, Real.pi_pos]
  have hcoslo : (39/40 : ℝ) ≤ Real.cos v := by
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hv0 hβπ hvβ
    have hβcos : Real.cos coarseAngleBeta = 39/40 := by
      unfold coarseAngleBeta
      exact Real.cos_arccos (by norm_num) (by norm_num)
    rwa [hβcos] at hc
  have hcoshi : Real.cos v ≤ 1 := Real.cos_le_one _
  unfold coarseAngleDeficit
  constructor <;> linarith

theorem coarseAngleArgument_sq (v : ℝ) :
    coarseAngleArgument v ^ 2 =
      coarseAngleDeficit v*(1+5*coarseAngleDeficit v)/4 := by
  have hhalf : Real.sin (v/2)^2 = (1-Real.cos v)/2 := by
    convert Real.sin_sq_eq_half_sub (v/2) using 1 <;> ring
  unfold coarseAngleArgument
  have harg : 0 ≤ 1+5*coarseAngleDeficit v := by
    -- The identity is used on the nonnegative-deficit arc.
    have hcos : Real.cos v ≤ 1 := Real.cos_le_one _
    unfold coarseAngleDeficit
    linarith
  rw [mul_pow, Real.sq_sqrt harg, hhalf]
  unfold coarseAngleDeficit
  ring

theorem coarseAngleArgument_range
    {v : ℝ} (hv0 : 0 ≤ v) (hvβ : v ≤ coarseAngleBeta) :
    0 ≤ coarseAngleArgument v ∧ coarseAngleArgument v ≤ 1/8 := by
  obtain ⟨he0,heδ⟩ := coarseAngleDeficit_range hv0 hvβ
  have hvπ : v ≤ Real.pi :=
    hvβ.trans (by linarith [coarseAngleBeta_range.2, Real.pi_pos])
  have hsin : 0 ≤ Real.sin (v/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have harg0 : 0 ≤ 1+5*coarseAngleDeficit v := by linarith
  have hu0 : 0 ≤ coarseAngleArgument v := by
    unfold coarseAngleArgument
    exact mul_nonneg hsin (Real.sqrt_nonneg _)
  have he2 : coarseAngleDeficit v ^ 2 ≤ (1/20 : ℝ)^2 :=
    (sq_le_sq₀ he0 (by norm_num)).mpr heδ
  have huSq := coarseAngleArgument_sq v
  have huSqLe : coarseAngleArgument v ^ 2 ≤ (1/8 : ℝ)^2 := by
    rw [huSq]
    nlinarith [he2]
  exact ⟨hu0, (sq_le_sq₀ hu0 (by norm_num)).mp huSqLe⟩

end SpringerLean

#print axioms SpringerLean.coarseAngleDeficit_range
#print axioms SpringerLean.coarseAngleArgument_sq
#print axioms SpringerLean.coarseAngleArgument_range
