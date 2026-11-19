import SpringerLean.Round722ActualTopRightTrace
import SpringerLean.Round718CompactCircleMaximum

open Set Metric

namespace SpringerLean
set_option Elab.async false
set_option autoImplicit false

def complexClosedRectangle (a b c d : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc a b ∧ z.im ∈ Icc c d}

theorem complexClosedRectangle_isCompact (a b c d : ℝ) :
    IsCompact (complexClosedRectangle a b c d) := by
  have heq : complexClosedRectangle a b c d =
      Complex.equivRealProdCLM.symm '' (Icc a b ×ˢ Icc c d) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), hz, ?_⟩
      simp only [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im]
    · rintro ⟨p, hp, rfl⟩
      change p.1 ∈ Icc a b ∧ p.2 ∈ Icc c d at hp
      simpa only [complexClosedRectangle, mem_setOf_eq,
        Complex.equivRealProdCLM_symm_apply_re,
        Complex.equivRealProdCLM_symm_apply_im] using hp
  rw [heq]
  exact (isCompact_Icc.prod isCompact_Icc).image Complex.equivRealProdCLM.symm.continuous

theorem mem_interior_complexClosedRectangle_of_strict
    {a b c d : ℝ} {z : ℂ}
    (ha : a < z.re) (hb : z.re < b) (hc : c < z.im) (hd : z.im < d) :
    z ∈ interior (complexClosedRectangle a b c d) := by
  let O : Set ℂ := {w | (a < w.re ∧ w.re < b) ∧ (c < w.im ∧ w.im < d)}
  have hO : IsOpen O :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (hO.mem_nhds ⟨⟨ha, hb⟩, hc, hd⟩)
    (fun w hw => ⟨⟨hw.1.1.le, hw.1.2.le⟩, hw.2.1.le, hw.2.2.le⟩)

/-- Every boundary point lies on one of the four actual rectangle edges.
This is separate from any estimate on a top function at those edges. -/
theorem complexClosedRectangle_frontier_edges
    {a b c d : ℝ} {z : ℂ} (hz : z ∈ frontier (complexClosedRectangle a b c d)) :
    z ∈ complexClosedRectangle a b c d ∧
      (z.re = a ∨ z.re = b ∨ z.im = c ∨ z.im = d) := by
  have hK := complexClosedRectangle_isCompact a b c d
  have hzK : z ∈ complexClosedRectangle a b c d := by
    have h := frontier_subset_closure hz
    rwa [hK.isClosed.closure_eq] at h
  refine ⟨hzK, ?_⟩
  by_cases ha : z.re = a
  · exact Or.inl ha
  by_cases hb : z.re = b
  · exact Or.inr (Or.inl hb)
  by_cases hc : z.im = c
  · exact Or.inr (Or.inr (Or.inl hc))
  by_cases hd : z.im = d
  · exact Or.inr (Or.inr (Or.inr hd))
  have hza : a < z.re := (lt_or_eq_of_le hzK.1.1).resolve_right (fun h => ha h.symm)
  have hzb : z.re < b := (lt_or_eq_of_le hzK.1.2).resolve_right hb
  have hzc : c < z.im := (lt_or_eq_of_le hzK.2.1).resolve_right (fun h => hc h.symm)
  have hzd : z.im < d := (lt_or_eq_of_le hzK.2.2).resolve_right hd
  exact (show z ∉ interior (complexClosedRectangle a b c d) from hz.2)
    (mem_interior_complexClosedRectangle_of_strict hza hzb hzc hzd) |>.elim

end SpringerLean

#print axioms SpringerLean.complexClosedRectangle_isCompact
#print axioms SpringerLean.complexClosedRectangle_frontier_edges
