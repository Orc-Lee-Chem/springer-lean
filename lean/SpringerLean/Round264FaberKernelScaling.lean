import SpringerLean.Round263RegularizedGrunsky

namespace SpringerLean
open PowerSeries

theorem formal_logOf_rescale
    {A : Type*} [CommRing A] [Algebra ℚ A]
    (a : A) (f : PowerSeries A) (hf : PowerSeries.constantCoeff f = 1) :
    PowerSeries.rescale a (PowerSeries.logOf f) =
      PowerSeries.logOf (PowerSeries.rescale a f) := by
  have hsubst : PowerSeries.HasSubst (f - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hf])
  simp only [PowerSeries.logOf_eq]
  rw [PowerSeries.rescale_eq_subst a ((PowerSeries.log A).subst (f - 1)),
    PowerSeries.subst_comp_subst_apply hsubst (PowerSeries.HasSubst.smul_X' a),
    ← PowerSeries.rescale_eq_subst a (f - 1), map_sub, map_one]

/-- Simultaneous scaling of the two reciprocal variables. -/
noncomputable def formalKernelRescale (a : ℂ) :
    PowerSeries (PowerSeries ℂ) →+* PowerSeries (PowerSeries ℂ) :=
  (PowerSeries.map (PowerSeries.rescale a)).comp
    (PowerSeries.rescale (PowerSeries.C a))

theorem formalKernelRescale_coeff
    (a : ℂ) (Q : PowerSeries (PowerSeries ℂ)) (i j : ℕ) :
    PowerSeries.coeff i (PowerSeries.coeff j (formalKernelRescale a Q)) =
      a ^ (i + j) * PowerSeries.coeff i (PowerSeries.coeff j Q) := by
  simp only [formalKernelRescale, RingHom.comp_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_rescale,
    ← map_pow, PowerSeries.coeff_C_mul]
  rw [pow_add]
  ring

theorem formalKernelRescale_logOf
    (a : ℂ) (Q : PowerSeries (PowerSeries ℂ))
    (hQ : PowerSeries.constantCoeff Q = 1) :
    formalKernelRescale a (PowerSeries.logOf Q) =
      PowerSeries.logOf (formalKernelRescale a Q) := by
  unfold formalKernelRescale
  simp only [RingHom.comp_apply]
  rw [formal_logOf_rescale _ Q hQ,
    formal_logOf_map (PowerSeries.rescale a) _]
  simp [← PowerSeries.coeff_zero_eq_constantCoeff, hQ]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hQ

theorem rescaleExterior_formalFaberKernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) :
    formalFaberKernel (exteriorFormalForward (rescaleExterior s F)) =
      formalKernelRescale (s : ℂ) (formalFaberKernel (exteriorFormalForward F)) := by
  ext j i
  rw [formalKernelRescale_coeff]
  cases j with
  | zero =>
      simp [PowerSeries.coeff_zero_eq_constantCoeff]
  | succ j =>
      cases i with
      | zero =>
          simp [PowerSeries.coeff_zero_eq_constantCoeff]
      | succ i =>
          simp only [formalFaberKernel_coeff_succ,
            formalFaberKernelRow_coeff_succ, exteriorFormalForward_coeff,
            rescaleExterior_forwardCoeff F hc hs]
          congr 2 <;> omega

/-- Exact all-order scaling of the same actual map's logarithmic kernel. -/
theorem rescaleExterior_formalGrunskyKernel
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) :
    exteriorFormalGrunskyKernel (rescaleExterior s F) =
      formalKernelRescale (s : ℂ) (exteriorFormalGrunskyKernel F) := by
  unfold exteriorFormalGrunskyKernel
  rw [rescaleExterior_formalFaberKernel F hc hs]
  have hlog := formalKernelRescale_logOf (s : ℂ)
    (1 - formalFaberKernel (exteriorFormalForward F)) (by simp)
  rw [map_sub, map_one] at hlog
  rw [← hlog, map_neg]

theorem rescaleExterior_formalGrunskyCoeff
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs : 0 < s) (i j : ℕ) :
    PowerSeries.coeff i
        (PowerSeries.coeff j (exteriorFormalGrunskyKernel (rescaleExterior s F))) =
      (s : ℂ) ^ (i + j) * PowerSeries.coeff i
        (PowerSeries.coeff j (exteriorFormalGrunskyKernel F)) := by
  rw [rescaleExterior_formalGrunskyKernel F hc hs,
    formalKernelRescale_coeff]

end SpringerLean
