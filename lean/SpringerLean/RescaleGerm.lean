import SpringerLean.Lemma31Prelude
import SpringerLean.Rescale

open scoped Topology
open scoped ComplexConjugate

namespace SpringerLean

/-- The centered germ of the manuscript's regular dilate comes from the same
actual exterior function as all the other coefficient interfaces. -/
theorem rescaleExterior_forwardGerm (s : ℝ) (hs : 0 < s) (F : ℂ → ℂ) (u : ℂ) :
    exteriorForwardGerm (rescaleExterior s F) u =
      (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * u) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  by_cases hu : u = 0
  · subst u
    simp [exteriorForwardGerm]
  · have hsu : (s : ℂ) * u ≠ 0 := mul_ne_zero hs0 hu
    simp only [exteriorForwardGerm, if_neg hu, if_neg hsu, rescaleExterior]
    rw [mul_inv_rev]
    field_simp

/-- A regular dilate belongs to the original exterior class. -/
theorem rescaleExterior_centeredExteriorUnivalent
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    CenteredExteriorUnivalent (rescaleExterior s F) := by
  have hsub : exteriorDisk ⊆ exteriorAbove s := by
    intro z hz
    exact lt_trans hs1 hz
  have hF : ∀ z ∈ exteriorDisk, AnalyticAt ℂ F z := by
    intro z hz
    exact hc.1.analyticAt (exteriorDisk_isOpen.mem_nhds hz)
  refine ⟨?_, (rescaleExterior_injOn hs0 hc.2.1).mono hsub, ?_⟩
  · intro z hz
    exact (rescaleExterior_analyticAt hs0 hF (hsub hz)).differentiableAt.differentiableWithinAt
  · have hinner : AnalyticAt ℂ (fun u : ℂ => (s : ℂ) * u) 0 := by fun_prop
    have hcomp : AnalyticAt ℂ
        (fun u : ℂ => exteriorForwardGerm F ((s : ℂ) * u)) 0 := by
      simpa only [Function.comp_def] using
        (hc.2.2).comp_of_eq hinner (by simp)
    have hscaled : AnalyticAt ℂ
        (fun u : ℂ => (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * u)) 0 := by
      fun_prop
    convert hscaled using 1
    funext u
    exact rescaleExterior_forwardGerm s hs0 F u

/-- The derivative-read Laurent coefficients of the actual regular dilate. -/
theorem rescaleExterior_forwardCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) (n : ℕ) :
    exteriorForwardCoeff (rescaleExterior s F) n =
      (s : ℂ) ^ (n + 1) * exteriorForwardCoeff F n := by
  have hinner : AnalyticAt ℂ (fun u : ℂ => (s : ℂ) * u) 0 := by fun_prop
  have hnear : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun j : ℕ => exteriorForwardCoeff F j * ((s : ℂ) * u) ^ j)
        (exteriorForwardGerm F ((s : ℂ) * u)) := by
    have hevent : ∀ᶠ t : ℂ in 𝓝 ((s : ℂ) * 0),
        HasSum (fun j : ℕ => exteriorForwardCoeff F j * t ^ j)
          (exteriorForwardGerm F t) := by
      simpa using exteriorForwardGerm_hasSum_coeff F hc.2.2
    simpa only [Function.comp_def] using
      hinner.continuousAt.tendsto.eventually hevent
  have hsums : ∀ᶠ u : ℂ in 𝓝 0,
      HasSum (fun j : ℕ =>
        ((s : ℂ) ^ (j + 1) * exteriorForwardCoeff F j) * u ^ j)
        (exteriorForwardGerm (rescaleExterior s F) u) := by
    filter_upwards [hnear] with u hu
    have h := hu.mul_left (s : ℂ)
    convert h using 1
    · funext j
      simp only [mul_pow, pow_succ]
      ring
    · exact rescaleExterior_forwardGerm s hs F u
  exact exteriorForwardCoeff_eq_of_hasSum
    (rescaleExterior s F)
    (fun j => (s : ℂ) ^ (j + 1) * exteriorForwardCoeff F j) hsums n

/-- On the unit circle the harmonic filling agrees with the genuine dilate. -/
theorem rescaleExterior_unitCircle_eq_harmonic
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : ‖z‖ = 1) :
    rescaleExterior s F z =
      z + (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * conj z) := by
  have hz0 : z ≠ 0 := by
    intro heq
    simp [heq] at hz
  have h := rescaleExterior_forwardGerm s hs F z⁻¹
  rw [exteriorForwardGerm_punctured _ (inv_ne_zero hz0), inv_inv,
    Complex.inv_eq_conj hz] at h
  exact (sub_eq_iff_eq_add.mp h).trans (by ring)

/-- The formal forward factor of a regular dilate is the rescaling of the
factor belonging to the original actual map. -/
theorem rescaleExterior_formalPhi
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) :
    formalExteriorPhi (exteriorFormalForward (rescaleExterior s F)) =
      PowerSeries.rescale (s : ℂ)
        (formalExteriorPhi (exteriorFormalForward F)) := by
  ext j
  cases j with
  | zero => simp [formalExteriorPhi]
  | succ k =>
      simp only [formalExteriorPhi, map_add, PowerSeries.coeff_rescale,
        map_one, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one,
        Nat.succ_ne_zero, ite_false, zero_add]
      rw [exteriorFormalForward_coeff, exteriorFormalForward_coeff,
        rescaleExterior_forwardCoeff F hc hs]

/-- All actual inverse coefficients scale by their Laurent order. -/
theorem rescaleExterior_inverseCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    exteriorInverseCoeff (rescaleExterior s F) n =
      (s : ℂ) ^ (n + 1) * exteriorInverseCoeff F n := by
  have hclass := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  have h1 := exteriorInverseCoeff_mul_eq_formalResidue
    (rescaleExterior s F) hclass n hn
  have h2 := exteriorInverseCoeff_mul_eq_formalResidue F hc n hn
  have hres : exteriorFormalResidue (rescaleExterior s F) n =
      (s : ℂ) ^ (n + 1) * exteriorFormalResidue F n := by
    simp only [exteriorFormalResidue, rescaleExterior_formalPhi F hc hs0,
      ← map_pow, PowerSeries.coeff_rescale]
  rw [hres, ← h2] at h1
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  apply mul_left_cancel₀ hn0
  calc
    (n : ℂ) * exteriorInverseCoeff (rescaleExterior s F) n =
        (s : ℂ) ^ (n + 1) * ((n : ℂ) * exteriorInverseCoeff F n) := h1
    _ = (n : ℂ) * ((s : ℂ) ^ (n + 1) * exteriorInverseCoeff F n) := by ring

/-- The regular correction `g_s(u)=s g(su)` and its harmonic filling. -/
noncomputable def regularForwardGerm (s : ℝ) (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * u)

noncomputable def regularHarmonic (s : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  z + regularForwardGerm s F (conj z)

theorem regularForwardGerm_eq_actual (s : ℝ) (hs : 0 < s) (F : ℂ → ℂ) :
    regularForwardGerm s F = exteriorForwardGerm (rescaleExterior s F) := by
  funext u
  exact (rescaleExterior_forwardGerm s hs F u).symm

theorem regularHarmonic_unitCircle_eq_actual
    (F : ℂ → ℂ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : ‖z‖ = 1) :
    regularHarmonic s F z = rescaleExterior s F z := by
  rw [regularHarmonic, regularForwardGerm,
    rescaleExterior_unitCircle_eq_harmonic F hs hz]

/-- The regular correction is analytic on the enlarged disk `|u|<1/s`. -/
theorem regularForwardGerm_analyticOnNhd
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) :
    AnalyticOnNhd ℂ (regularForwardGerm s F)
      (Metric.ball 0 s⁻¹) := by
  intro u hu
  have hnorm : ‖(s : ℂ) * u‖ < 1 := by
    have hu' : ‖u‖ < s⁻¹ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hu
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    have hh : ‖u‖ * s < 1 :=
      (lt_div_iff₀ hs).mp (show ‖u‖ < 1 / s by simpa [one_div] using hu')
    nlinarith
  have harg : (s : ℂ) * u ∈ Metric.ball (0 : ℂ) 1 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hnorm
  have hf := exteriorForwardGerm_analyticOnNhd_unitBall F hc
    ((s : ℂ) * u) harg
  have hinner : AnalyticAt ℂ (fun v : ℂ => (s : ℂ) * v) u := by fun_prop
  have hcomp : AnalyticAt ℂ
      (fun v : ℂ => exteriorForwardGerm F ((s : ℂ) * v)) u := by
    simpa only [Function.comp_def] using hf.comp hinner
  have hscaled : AnalyticAt ℂ
      (fun v : ℂ => (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * v)) u := by
    fun_prop
  change AnalyticAt ℂ
    (fun v : ℂ => (s : ℂ) * exteriorForwardGerm F ((s : ℂ) * v)) u
  exact hscaled


end SpringerLean
