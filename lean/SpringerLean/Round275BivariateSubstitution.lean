import SpringerLean.Round270ActualTaylorComposition

namespace SpringerLean
open PowerSeries

noncomputable def formalSubstRingHom {A : Type*} [CommRing A]
    (H : PowerSeries A) (hH : PowerSeries.constantCoeff H = 0) :
    PowerSeries A →+* PowerSeries A where
  toFun := fun f => f.subst H
  map_zero' := by
    simpa only [map_zero] using (PowerSeries.subst_C (0 : A) (a := H))
  map_one' := by
    simpa only [map_one] using (PowerSeries.subst_C (1 : A) (a := H))
  map_add' := PowerSeries.subst_add (PowerSeries.HasSubst.of_constantCoeff_zero' hH)
  map_mul' := PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hH)

@[simp] theorem formalSubstRingHom_apply {A : Type*} [CommRing A]
    (H : PowerSeries A) (hH : PowerSeries.constantCoeff H = 0) (f : PowerSeries A) :
    formalSubstRingHom H hH f = f.subst H := rfl

/-- Simultaneous substitution of the same zero-constant inverse coordinate
into both variables. Only normalized formal substitution is used. -/
noncomputable def formalKernelSubst (H : PowerSeries ℂ)
    (hH : PowerSeries.constantCoeff H = 0) :
    PowerSeries (PowerSeries ℂ) →+* PowerSeries (PowerSeries ℂ) :=
  (formalSubstRingHom (PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) H)
    (by change PowerSeries.C (PowerSeries.constantCoeff H) = 0; rw [hH, map_zero])).comp
      (PowerSeries.map (formalSubstRingHom H hH))

theorem formalKernelSubst_C (H : PowerSeries ℂ)
    (hH : PowerSeries.constantCoeff H = 0) (f : PowerSeries ℂ) :
    formalKernelSubst H hH (PowerSeries.C f) = PowerSeries.C (f.subst H) := by
  simp only [formalKernelSubst, RingHom.comp_apply, PowerSeries.map_C,
    formalSubstRingHom_apply, PowerSeries.subst_C]
  rfl

theorem formalKernelSubst_X (H : PowerSeries ℂ)
    (hH : PowerSeries.constantCoeff H = 0) :
    formalKernelSubst H hH PowerSeries.X =
      PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) H := by
  simp only [formalKernelSubst, RingHom.comp_apply, PowerSeries.map_X,
    formalSubstRingHom_apply]
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero'
    (by change PowerSeries.C (PowerSeries.constantCoeff H) = 0; rw [hH, map_zero]))

theorem formalKernelSubst_map_C (H : PowerSeries ℂ)
    (hH : PowerSeries.constantCoeff H = 0) (f : PowerSeries ℂ) :
    formalKernelSubst H hH (PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) f) =
      PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) (f.subst H) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hm : PowerSeries.map (formalSubstRingHom H hH)
      (PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) f) =
      PowerSeries.map (PowerSeries.C : ℂ →+* PowerSeries ℂ) f := by
    ext1 n
    simp only [PowerSeries.coeff_map]
    exact PowerSeries.subst_C (PowerSeries.coeff n f) (a := H)
  simp only [formalKernelSubst, RingHom.comp_apply, hm, formalSubstRingHom_apply]
  exact (PowerSeries.map_subst hs f).symm

theorem formalKernelSubst_logOf (H : PowerSeries ℂ)
    (hH : PowerSeries.constantCoeff H = 0)
    (f : PowerSeries (PowerSeries ℂ)) (hf : PowerSeries.constantCoeff f = 1) :
    formalKernelSubst H hH (PowerSeries.logOf f) =
      PowerSeries.logOf (formalKernelSubst H hH f) := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hH
  unfold formalKernelSubst
  simp only [RingHom.comp_apply]
  simp only [formalSubstRingHom_apply]
  rw [formal_logOf_map (formalSubstRingHom H hH) f hf,
    formal_logOf_subst]
  · change formalSubstRingHom H hH (PowerSeries.constantCoeff f) = 1
    rw [hf, map_one]
  · change PowerSeries.C (PowerSeries.constantCoeff H) = 0
    rw [hH, map_zero]

end SpringerLean
