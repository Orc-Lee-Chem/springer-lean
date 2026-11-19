import Mathlib.Analysis.Complex.HasPrimitives

open Set Metric Filter Complex
open scoped Topology Interval

namespace SpringerLean

/-- A finite walk whose edges are horizontal or vertical closed
segments contained in the domain. -/
inductive RectilinearWalk (U : Set ℂ) (a : ℂ) : ℂ → Type
  | point (ha : a ∈ U) : RectilinearWalk U a a
  | step {z w : ℂ} (p : RectilinearWalk U a z) (axis : z.re = w.re ∨ z.im = w.im)
      (edge : Rectangle z w ⊆ U) : RectilinearWalk U a w

namespace RectilinearWalk

variable {U : Set ℂ} {a b c : ℂ}

theorem mem_target : RectilinearWalk U a b → b ∈ U
  | .point ha => ha
  | .step _ _ he => he ⟨right_mem_uIcc,right_mem_uIcc⟩

def append (p : RectilinearWalk U a b) : ∀ {c}, RectilinearWalk U b c → RectilinearWalk U a c
  | _, .point _ => p
  | _, .step q ha he => (append p q).step ha he

private theorem rectangle_reverse (z w : ℂ) : Rectangle w z = Rectangle z w := by
  unfold Rectangle
  rw [uIcc_comm w.re z.re,uIcc_comm w.im z.im]

def reverse : ∀ {b}, RectilinearWalk U a b → RectilinearWalk U b a
  | _, .point ha => .point ha
  | _, .step (z := z) (w := w) p ha he =>
    let hstep : RectilinearWalk U w z :=
      (point (a := w) (he ⟨right_mem_uIcc,right_mem_uIcc⟩)).step
        (ha.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm))
        (by rwa [rectangle_reverse z w])
    hstep.append p.reverse

noncomputable def integral (f : ℂ → ℂ) : ∀ {b}, RectilinearWalk U a b → ℂ
  | _, .point _ => 0
  | _, .step (z := z) (w := w) p _ _ => integral f p + wedgeIntegral z w f

theorem integral_append (f : ℂ → ℂ) (p : RectilinearWalk U a b) (q : RectilinearWalk U b c) :
    integral f (p.append q) = integral f p + integral f q := by
  induction q with
  | point => simp [append,integral]
  | step q ha he ih => simp only [append,integral,ih,add_assoc]

private theorem wedgeIntegral_axis_reverse (f : ℂ → ℂ) {z w : ℂ}
    (ha : z.re = w.re ∨ z.im = w.im) : wedgeIntegral w z f = -wedgeIntegral z w f := by
  rcases ha with h | h
  · simp only [wedgeIntegral,h,intervalIntegral.integral_same,zero_add,
      intervalIntegral.integral_symm w.im z.im,smul_neg,neg_neg]
  · simp only [wedgeIntegral,h,intervalIntegral.integral_same,smul_zero,add_zero,
      intervalIntegral.integral_symm w.re z.re,neg_neg]

theorem integral_reverse (f : ℂ → ℂ) (p : RectilinearWalk U a b) :
    integral f p.reverse = -integral f p := by
  induction p with
  | point => simp [reverse,integral]
  | step p ha he ih =>
    simp only [reverse,integral_append,integral,zero_add,ih,wedgeIntegral_axis_reverse f ha]
    abel

private theorem rectangle_wedge_first (z w : ℂ) :
    Rectangle z ((w.re:ℂ)+z.im*I) ⊆ Rectangle z w := by
  intro y hy
  simp only [Rectangle,mem_reProdIm,add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,
    I_re,I_im,mul_zero,mul_one,zero_mul,sub_zero,sub_self,add_zero,zero_add,uIcc_self,
    mem_singleton_iff] at hy ⊢
  exact ⟨hy.1,hy.2.symm ▸ left_mem_uIcc⟩

private theorem rectangle_wedge_second (z w : ℂ) :
    Rectangle ((w.re:ℂ)+z.im*I) w ⊆ Rectangle z w := by
  intro y hy
  simp only [Rectangle,mem_reProdIm,add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,
    I_re,I_im,mul_zero,mul_one,zero_mul,sub_zero,sub_self,add_zero,zero_add,uIcc_self,
    mem_singleton_iff] at hy ⊢
  exact ⟨hy.1.symm ▸ right_mem_uIcc,hy.2⟩

def wedge {z w : ℂ} (hs : Rectangle z w ⊆ U) : RectilinearWalk U z w :=
  let v : ℂ := (w.re:ℂ)+z.im*I
  let p : RectilinearWalk U z v := (point (hs ⟨left_mem_uIcc,left_mem_uIcc⟩)).step
    (Or.inr (by simp [v])) ((rectangle_wedge_first z w).trans hs)
  p.step (Or.inl (by simp [v])) ((rectangle_wedge_second z w).trans hs)

theorem integral_wedge (f : ℂ → ℂ) {z w : ℂ} (hs : Rectangle z w ⊆ U) :
    integral f (wedge hs) = wedgeIntegral z w f := by
  simp [wedge,integral,wedgeIntegral]

theorem rectangle_subset_ball_center {z w : ℂ} {r : ℝ} (hr : 0 < r) (hw : w ∈ ball z r) :
    Rectangle z w ⊆ ball z r := by
  apply Convex.rectangle_subset (convex_ball _ _) (mem_ball_self hr) hw
  · rw [mem_ball,Complex.dist_eq_re_im] at hw ⊢
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,mul_zero,mul_one,
      zero_mul,sub_zero,sub_self,add_zero,zero_add,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at *
    exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (w.re-z.re)])).trans_lt hw
  · rw [mem_ball,Complex.dist_eq_re_im] at hw ⊢
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,mul_zero,mul_one,
      zero_mul,sub_zero,sub_self,add_zero,zero_add,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at *
    exact (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (w.im-z.im)])).trans_lt hw

theorem nonempty_of_isOpen_isPreconnected
    (hU : IsOpen U) (hc : IsPreconnected U) (ha : a ∈ U) (hb : b ∈ U) :
    Nonempty (RectilinearWalk U a b) := by
  let A := {z | Nonempty (RectilinearWalk U a z)}
  have hs : A ⊆ U := fun _ ⟨p⟩ => p.mem_target
  have hopen : IsOpen A := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU z (hs hz)
    refine ⟨r,hr,fun w hw => ?_⟩
    obtain ⟨p⟩ := hz
    exact ⟨p.append (wedge ((rectangle_subset_ball_center hr hw).trans hsub))⟩
  have hcomp : IsOpen (U \ A) := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU z hz.1
    refine ⟨r,hr,fun w hw => ⟨hsub hw,fun h => ?_⟩⟩
    obtain ⟨p⟩ := h
    exact hz.2 ⟨p.append (wedge ((rectangle_subset_ball_center hr hw).trans hsub)).reverse⟩
  have hA : A ∩ (U \ A) = ∅ := by ext z; simp [and_comm, and_left_comm]
  have hcover : U ⊆ A ∪ (U \ A) := by
    intro z hz
    by_cases h : z ∈ A
    · exact Or.inl h
    · exact Or.inr ⟨hz,h⟩
  exact hc.subset_left_of_subset_union hopen hcomp (Set.disjoint_iff_inter_eq_empty.mpr hA)
    hcover ⟨a,ha,⟨point ha⟩⟩ hb

/-- It is enough to prove zero integrals over closed rectilinear
walks. The local disk primitive in mathlib then glues globally. -/
theorem isExactOn_of_closed_integrals_eq_zero
    (hU : IsOpen U) (hc : IsConnected U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hzero : ∀ z : ℂ, ∀ p : RectilinearWalk U z z, integral f p = 0) :
    IsExactOn f U := by
  classical
  obtain ⟨a,ha⟩ := hc.nonempty
  let path (z : ℂ) (hz : z ∈ U) :=
    Classical.choice (nonempty_of_isOpen_isPreconnected hU hc.isPreconnected ha hz)
  let P (z : ℂ) := if hz : z ∈ U then integral f (path z hz) else 0
  have hpath (z : ℂ) (hz : z ∈ U) (p : RectilinearWalk U a z) : P z = integral f p := by
    have h := hzero a ((path z hz).append p.reverse)
    rw [integral_append,integral_reverse,←sub_eq_add_neg,sub_eq_zero] at h
    simpa only [P,dif_pos hz] using h
  refine ⟨P,fun z hz => ?_⟩
  obtain ⟨r,hr,hsub⟩ := Metric.isOpen_iff.mp hU z hz
  have hD := hf.mono hsub
  have hp := hD.isConservativeOn.hasDerivAt_wedgeIntegral hD.continuousOn (mem_ball_self hr)
  apply (hp.const_add (P z)).congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds z hr] with w hw
  let q := wedge ((rectangle_subset_ball_center hr hw).trans hsub)
  rw [hpath w (hsub hw) ((path z hz).append q),integral_append,integral_wedge,
    ←hpath z hz (path z hz)]

end RectilinearWalk

end SpringerLean
