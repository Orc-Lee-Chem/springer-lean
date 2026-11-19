import SpringerLean.Round1553ThinAnnulusCubicScalar

namespace SpringerLean
set_option maxHeartbeats 640000

/-- The strict full-annulus scalar margin persists at an outer radius
strictly below one, where the actual harmonic filling is continuous. -/
theorem thinAnnulus_exists_truncated_cubic_margin
    {m : ℕ} (hm : 1500 ≤ m) {d : ℝ}
    (hd0 : 0 < d) (hD : (m:ℝ)*d ≤ 3/20) :
    let D := (m:ℝ)*d
    let a := 1-Real.sqrt d/16
    ∃ b : ℝ, a ≤ b ∧ b < 1 ∧
      D^3/30 < (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D*
        (b^m-a^m) := by
  dsimp only
  let D : ℝ := (m:ℝ)*d
  let a : ℝ := 1-Real.sqrt d/16
  let C : ℝ := (9/(100*Real.pi):ℝ)*(1-1/(m:ℝ))*D^2*Real.sqrt D
  have ha1 : a < 1 := by
    dsimp [a]
    have hs := Real.sqrt_pos.2 hd0
    linarith
  have hmargin := thinAnnulus_cubic_scalar_margin hm hd0 hD
  change D^3/30 < C*(1-a^m) at hmargin
  have hcont : ContinuousAt (fun b : ℝ => C*(b^m-a^m)) 1 := by fun_prop
  have hnear : ∀ᶠ b in nhdsWithin (1:ℝ) (Set.Iio 1),
      D^3/30 < C*(b^m-a^m) :=
    (hcont.tendsto.mono_left nhdsWithin_le_nhds).eventually
      (by simpa using (lt_mem_nhds hmargin))
  have habNear : ∀ᶠ b in nhds (1:ℝ), a < b := by
    exact lt_mem_nhds ha1
  have hab : ∀ᶠ b in nhdsWithin (1:ℝ) (Set.Iio 1), a < b :=
    habNear.filter_mono nhdsWithin_le_nhds
  have hbelow : ∀ᶠ b in nhdsWithin (1:ℝ) (Set.Iio 1), b < 1 :=
    self_mem_nhdsWithin
  obtain ⟨b, ⟨hb, hab'⟩, hnear'⟩ :=
    ((hbelow.and hab).and hnear).exists
  exact ⟨b, hab'.le, hb, hnear'⟩

end SpringerLean

#print axioms SpringerLean.thinAnnulus_exists_truncated_cubic_margin
