import SpringerLean.Round723ComplexRectangle

open MeasureTheory Set Metric Real

namespace SpringerLean

/-- Maximum principle on the strip rectangle. An upper-edge point
may be controlled by moving inward, as happens at an omitted radius
for the clipped Green top integral. -/
theorem strip_le_of_local_submean_and_flat_top
    (f : ℂ → ℝ) (a b ε : ℝ) (hε : 0 < ε)
    (hf : ContinuousOn f (complexClosedRectangle a b 0 π))
    (hsub : ∀ z : ℂ, 0 < z.im → z.im < π →
      ∃ δ > 0, ∀ r > 0, r < δ → f z ≤ circleAverage f z r)
    (hedge : ∀ z ∈ complexClosedRectangle a b 0 π,
      z.re = a ∨ z.re = b ∨ z.im = 0 → f z ≤ ε)
    (htop : ∀ z ∈ complexClosedRectangle a b 0 π, z.im = π →
      f z ≤ ε ∨ ∃ d : ℝ, 0 < d ∧ ∀ s : ℝ, 0 < s → s < d → f z ≤ f (z-(s:ℂ)*Complex.I)) :
    ∀ z ∈ complexClosedRectangle a b 0 π, f z ≤ ε*(1+π) := by
  let K := complexClosedRectangle a b 0 π
  let κ := ε/(4*π)
  let q (z : ℂ) := κ*z.im^2-ε*z.im
  let W (z : ℂ) := f z+q z
  have hκ : 0 < κ := div_pos hε (by positivity)
  have hκeq : κ*(4*π) = ε := div_mul_cancel₀ _ (by positivity)
  have hq (z : ℂ) (hz : z ∈ K) : -ε*π ≤ q z ∧ q z ≤ 0 := by
    have hh : z.im ∈ Icc (0:ℝ) π := hz.2
    have hle := mul_le_mul_of_nonneg_left hh.2 hκ.le
    have hn := mul_nonneg hh.1 (sub_nonneg.mpr (show κ*z.im ≤ ε by nlinarith only [hle,hκeq,hε]))
    have hp := mul_le_mul_of_nonneg_left hh.2 hε.le
    dsimp [q]
    constructor <;> nlinarith only [hn,hp,mul_nonneg hκ.le (sq_nonneg z.im)]
  intro z₀ hz₀
  have hK : IsCompact K := complexClosedRectangle_isCompact _ _ _ _
  have hqc : Continuous q := by unfold q; fun_prop
  have hW : ContinuousOn W K := hf.add hqc.continuousOn
  obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn ⟨z₀,hz₀⟩ hW
  have hWmax : W z ≤ ε := by
    by_contra! hbad
    have hn₁ : z.re ≠ a := fun he => (not_lt_of_ge (by
      dsimp [W]; linarith only [hedge z hz (Or.inl he),(hq z hz).2])) hbad
    have hn₂ : z.re ≠ b := fun he => (not_lt_of_ge (by
      dsimp [W]; linarith only [hedge z hz (Or.inr (Or.inl he)),(hq z hz).2])) hbad
    have hn₀ : z.im ≠ 0 := fun he => (not_lt_of_ge (by
      dsimp [W]; linarith only [hedge z hz (Or.inr (Or.inr he)),(hq z hz).2])) hbad
    have hnπ : z.im ≠ π := by
      intro he
      rcases htop z hz he with h | ⟨d,hd,hmove⟩
      · dsimp [W] at hbad
        linarith only [hbad,h,(hq z hz).2]
      let s := min d π/2
      have hs : 0 < s := half_pos (lt_min hd pi_pos)
      have hsd : s < d := by dsimp [s]; linarith [min_le_left d π]
      have hsπ : s < π := by dsimp [s]; linarith [min_le_right d π,pi_pos]
      let w := z-(s:ℂ)*Complex.I
      have hwre : w.re = z.re := by simp [w,Complex.sub_re,Complex.mul_re]
      have hwim : w.im = π-s := by simp [w,Complex.sub_im,Complex.mul_im,he]
      have hw : w ∈ K := by
        change w.re ∈ Icc a b ∧ w.im ∈ Icc 0 π
        rw [hwre,hwim]
        exact ⟨hz.1,⟨sub_nonneg.mpr hsπ.le,sub_le_self _ hs.le⟩⟩
      have hqW : q z < q w := by
        dsimp [q]
        rw [he,hwim]
        have heq : κ*(π-s)^2-ε*(π-s)-(κ*π^2-ε*π) = s*(ε/2+κ*s) := by
          have ht : κ*π = ε/4 := by linarith only [hκeq]
          linear_combination -2*s*ht
        have hpos : 0 < s*(ε/2+κ*s) := mul_pos hs (add_pos_of_pos_of_nonneg (half_pos hε)
          (mul_nonneg hκ.le hs.le))
        linarith only [heq,hpos]
      have hfw : f z ≤ f w := hmove s hs hsd
      have hMw := hmax hw
      dsimp [W] at hMw
      linarith only [hMw,hfw,hqW]
    have hzin : z ∈ interior K := mem_interior_complexClosedRectangle_of_strict
      (lt_of_le_of_ne hz.1.1 (Ne.symm hn₁)) (lt_of_le_of_ne hz.1.2 hn₂)
      (lt_of_le_of_ne hz.2.1 (Ne.symm hn₀)) (lt_of_le_of_ne hz.2.2 hnπ)
    obtain ⟨δ,hδ,hmean⟩ := hsub z (lt_of_le_of_ne hz.2.1 (Ne.symm hn₀)) (lt_of_le_of_ne hz.2.2 hnπ)
    obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzin)
    let r := min δ d/2
    have hr : 0 < r := half_pos (lt_min hδ hd)
    have hrδ : r < δ := by dsimp [r]; linarith [min_le_left δ d]
    have hrd : r < d := by dsimp [r]; linarith [min_le_right δ d]
    have hsph : sphere z |r| ⊆ K := by
      intro w hw
      apply hball
      have he : dist w z = r := by simpa only [mem_sphere,abs_of_pos hr] using hw
      exact Metric.mem_ball.mpr (he ▸ hrd)
    have hfi := (hf.mono hsph).circleIntegrable'
    have hqi := hqc.continuousOn.circleIntegrable hr.le (c := z)
    have hsqi : CircleIntegrable (fun z : ℂ => κ*z.im^2) z r :=
      (by fun_prop : Continuous (fun z : ℂ => κ*z.im^2)).continuousOn.circleIntegrable hr.le
    have hli : CircleIntegrable (fun z : ℂ => ε*z.im) z r :=
      (by fun_prop : Continuous (fun z : ℂ => ε*z.im)).continuousOn.circleIntegrable hr.le
    have hqeq : circleAverage q z r = q z+κ*(r^2/2) := by
      unfold q
      rw [circleAverage_fun_sub hsqi hli,
        show (fun z : ℂ => κ*z.im^2) = κ • (fun z : ℂ => z.im^2) from rfl,
        show (fun z : ℂ => ε*z.im) = ε • (fun z : ℂ => z.im) from rfl,
        circleAverage_smul,circleAverage_smul,circleAverage_im_sq,circleAverage_im]
      simp only [smul_eq_mul]
      ring
    have hWeq : circleAverage W z r = circleAverage f z r+q z+κ*(r^2/2) := by
      unfold W
      rw [circleAverage_fun_add hfi hqi,hqeq]
      ring
    have hstrict : W z < circleAverage W z r := by
      rw [hWeq]
      dsimp [W]
      linarith only [hmean r hr hrδ,show 0 < κ*(r^2/2) by positivity]
    have hupper := circleAverage_mono_on_of_le_circle (hfi.add hqi) (fun w hw => hmax (hsph hw))
    exact (not_lt_of_ge hupper) hstrict
  have hzle := (hmax hz₀).trans hWmax
  dsimp [W] at hzle
  linarith only [hzle,(hq z₀ hz₀).1]

end SpringerLean
