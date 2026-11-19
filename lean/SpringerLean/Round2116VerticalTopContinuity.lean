import SpringerLean.Round2115PeriodicTopStability
import SpringerLean.Round723ComplexRectangle

open Set Metric Real

namespace SpringerLean

/-- The top mass on a vertical period, in logarithmic coordinates. -/
noncomputable def verticalPeriodicTop (u : ℂ → ℝ) (T : ℝ) (z : ℂ) : ℝ :=
  periodicTopIntegral (fun t : ℝ => u ((z.re:ℂ)+(t:ℂ)*Complex.I)) T (2*z.im)

theorem verticalPeriodicTop_continuousOn
    (u : ℂ → ℝ) (hu : Continuous u) (h₀ : ∀ z, 0 ≤ u z)
    (T : ℝ) (hT : 0 < T)
    (hp : ∀ x : ℝ, Function.Periodic (fun t : ℝ => u ((x:ℂ)+(t:ℂ)*Complex.I)) T) :
    ContinuousOn (verticalPeriodicTop u T) {z : ℂ | 0 ≤ z.im ∧ z.im ≤ T/2} := by
  intro z hz
  let x := z.re
  let R := complexClosedRectangle (x-1) (x+1) 0 T
  have hR : IsCompact R := complexClosedRectangle_isCompact _ _ _ _
  obtain ⟨B,hB⟩ := (hR.image hu).isBounded.exists_norm_le
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hbound (w : ℂ) (hw : w ∈ R) : 0 ≤ u w ∧ u w ≤ M :=
    ⟨h₀ w, (le_abs_self _).trans ((hB _ ⟨w,hw,rfl⟩).trans (le_max_left _ _))⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let e := ε/(4*T)
  have he : 0 < e := div_pos hε (by positivity)
  obtain ⟨δ,hδ,hδu⟩ := Metric.uniformContinuousOn_iff.mp
    (hR.uniformContinuousOn_of_continuous hu.continuousOn) e he
  let d := min 1 (min δ (ε/(8*(M+1))))
  have hd : 0 < d := lt_min zero_lt_one (lt_min hδ (div_pos hε (by positivity)))
  refine ⟨d,hd,?_⟩
  intro w hw hwd
  have hdist : ‖w-z‖ < d := by simpa only [dist_eq_norm] using hwd
  have hre : |w.re-z.re| ≤ ‖w-z‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w-z)
  have him : |w.im-z.im| ≤ ‖w-z‖ := by
    simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w-z)
  let f (t : ℝ) := u ((w.re:ℂ)+(t:ℂ)*Complex.I)
  let g (t : ℝ) := u ((x:ℂ)+(t:ℂ)*Complex.I)
  have hf : Continuous f := hu.comp (by fun_prop)
  have hg : Continuous g := hu.comp (by fun_prop)
  have hff (t : ℝ) (ht : t ∈ Ioc 0 T) : ((w.re:ℂ)+(t:ℂ)*Complex.I) ∈ R := by
    have h₁ := hre.trans_lt (hdist.trans_le (min_le_left _ _))
    have h₂ := abs_lt.mp h₁
    change ((_ : ℂ).re ∈ Icc (x-1) (x+1)) ∧ ((_ : ℂ).im ∈ Icc 0 T)
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_mul,zero_add,add_zero]
    exact ⟨⟨by dsimp [x]; linarith [h₂.1],by dsimp [x]; linarith [h₂.2]⟩,⟨ht.1.le,ht.2⟩⟩
  have hgg (t : ℝ) (ht : t ∈ Ioc 0 T) : ((x:ℂ)+(t:ℂ)*Complex.I) ∈ R := by
    change ((_ : ℂ).re ∈ Icc (x-1) (x+1)) ∧ ((_ : ℂ).im ∈ Icc 0 T)
    simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,zero_mul,zero_add,add_zero]
    exact ⟨⟨by linarith,by linarith⟩,⟨ht.1.le,ht.2⟩⟩
  have hclose (t : ℝ) (ht : t ∈ Ioc 0 T) : |f t-g t| < e := by
    have heq : dist ((w.re:ℂ)+(t:ℂ)*Complex.I) ((x:ℂ)+(t:ℂ)*Complex.I) = |w.re-z.re| := by
      rw [dist_eq_norm, show (w.re:ℂ)+(t:ℂ)*Complex.I-((x:ℂ)+(t:ℂ)*Complex.I) =
        ((w.re-z.re:ℝ):ℂ) by dsimp [x]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    have hlt := hδu _ (hff t ht) _ (hgg t ht) (by
      rw [heq]
      exact hre.trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _))))
    simpa only [Real.dist_eq] using hlt
  let m := 2*w.im
  let n := 2*z.im
  have hm : 0 ≤ m := by dsimp [m]; linarith [hw.1]
  have hmT : m ≤ T := by dsimp [m]; linarith [hw.2]
  have hn : 0 ≤ n := by dsimp [n]; linarith [hz.1]
  have hnT : n ≤ T := by dsimp [n]; linarith [hz.2]
  have hmclose : M*|m-n| ≤ ε/4 := by
    have hr : |w.im-z.im| ≤ ε/(8*(M+1)) := him.trans
      (hdist.le.trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hh := (le_div_iff₀ (show 0 < 8*(M+1) by positivity)).mp hr
    have hEq : |m-n| = 2*|w.im-z.im| := by
      dsimp [m,n]
      rw [show 2*w.im-2*z.im=2*(w.im-z.im) by ring,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    rw [hEq]
    nlinarith only [hh,abs_nonneg (w.im-z.im)]
  have hTe : T*e = ε/4 := by dsimp [e]; field_simp [hT.ne']
  have hfg := periodicTopIntegral_le_add_of_forall_le_add f g hf hg T m e hT hm hmT (hp w.re) he.le
    (fun t ht => by linarith [(abs_lt.mp (hclose t ht)).2])
  have hgf := periodicTopIntegral_le_add_of_forall_le_add g f hg hf T n e hT hn hnT (hp x) he.le
    (fun t ht => by linarith [(abs_lt.mp (hclose t ht)).1])
  have hgmn := periodicTopIntegral_le_add_of_mass g hg T M m n hT (hp x) hm hmT hn hnT hM
    (fun t ht => hbound _ (hgg t ht))
  have hfnm := periodicTopIntegral_le_add_of_mass f hf T M n m hT (hp w.re) hn hnT hm hmT hM
    (fun t ht => hbound _ (hff t ht))
  rw [abs_sub_comm n m] at hfnm
  change dist (periodicTopIntegral f T m) (periodicTopIntegral g T n) < ε
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith only [hfg,hgf,hgmn,hfnm,hTe,hmclose,hε]

end SpringerLean
