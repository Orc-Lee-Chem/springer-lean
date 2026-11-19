import SpringerLean.Round401EndpointChoices

open scoped ComplexConjugate Topology

namespace SpringerLean
set_option Elab.async false

/-- An opposite-half radius maximizer away from the cutting line is an
actual omitted point. The proof uses a supporting real functional of the
same compact omitted set, rather than boundary regularity. -/
theorem exteriorOmitted_half_maximizer_mem_of_strict
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (ξ P : ℂ)
    (hP : P ∈ convexHull ℝ (exteriorOmitted F))
    (hneg : (conj ξ * P).re < 0)
    (hmax : ∀ w ∈ convexHull ℝ (exteriorOmitted F),
      (conj ξ * w).re ≤ 0 → ‖w‖ ≤ ‖P‖) :
    P ∈ exteriorOmitted F := by
  let L : ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (conj P))
  obtain ⟨Q,hQ,hQmax⟩ := (exteriorOmitted_isCompact F hc).exists_isMaxOn
    (exteriorOmitted_nonempty F hc) L.continuous.continuousOn
  have hsupport : L P ≤ L Q := by
    have hs : exteriorOmitted F ⊆ L ⁻¹' Set.Iic (L Q) := fun w hw => hQmax hw
    exact convexHull_min hs ((convex_Iic (L Q)).linear_preimage L.toLinearMap) hP
  let u : ℝ → ℂ := fun t => (1-t) • P + t • Q
  have hcont : Continuous (fun t : ℝ => (conj ξ * u t).re) := by
    dsimp only [u]
    fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, (conj ξ * u t).re < 0 :=
    hcont.continuousAt.eventually (Iio_mem_nhds (by simpa [u] using hneg))
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let t : ℝ := min δ 1 / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htd : t < δ := by
    have hm := min_le_left δ (1 : ℝ)
    dsimp only [t]
    linarith [lt_min hδ zero_lt_one]
  have ht1 : t < 1 := by
    have hm := min_le_right δ (1 : ℝ)
    dsimp only [t]
    linarith
  have hnegU : (conj ξ * u t).re ≤ 0 :=
    (hball (by simpa [Real.dist_eq,abs_of_pos ht] using htd)).le
  have hu : u t ∈ convexHull ℝ (exteriorOmitted F) :=
    (convex_convexHull ℝ _) hP (subset_convexHull ℝ _ hQ)
      (by linarith) ht.le (by ring)
  have hnorm := hmax (u t) hu hnegU
  have hnorm2 : ‖u t‖ ^ 2 ≤ ‖P‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
  have hn (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa [Complex.normSq_apply,pow_two] using Complex.sq_norm z
  have hid : ‖u t‖ ^ 2 - ‖P‖ ^ 2 =
      2*t*(L Q-L P) + t^2*‖Q-P‖^2 := by
    rw [hn (u t),hn P,hn (Q-P)]
    simp [u,L,Complex.mul_re,Complex.smul_re,Complex.smul_im]
    ring
  have hz : ‖Q-P‖ ^ 2 = 0 := by
    have hp := mul_nonneg (show 0 ≤ 2*t by positivity) (sub_nonneg.mpr hsupport)
    have hq := sq_nonneg ‖Q-P‖
    nlinarith [sq_pos_of_pos ht]
  have hQP : Q = P := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  rwa [hQP] at hQ

end SpringerLean
