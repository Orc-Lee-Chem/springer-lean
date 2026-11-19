import SpringerLean.Round09Outer
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open scoped ComplexConjugate

namespace SpringerLean

/-- A smooth bump equal to one inside radius `T+1` and supported inside
radius `T+2`. -/
noncomputable def areaBump (T : ℝ) (hT : 0 ≤ T) : ContDiffBump (0 : ℂ) :=
  ⟨T + 1, T + 2, by linarith, by linarith⟩

/-- A smooth compactly supported replacement for the even polynomial area
weight `‖w‖^(2k-2)`. -/
noncomputable def evenWeightCutoff (T : ℝ) (hT : 0 ≤ T) (k : ℕ)
    (w : ℂ) : ℝ :=
  areaBump T hT w * Complex.normSq w ^ (k - 1)

theorem evenWeightCutoff_contDiff
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    ContDiff ℝ 1 (evenWeightCutoff T hT k) := by
  have hb : ContDiff ℝ 1 (areaBump T hT : ℂ → ℝ) :=
    (areaBump T hT).contDiff
  have hre : ContDiff ℝ 1 (fun w : ℂ => w.re) := by
    change ContDiff ℝ 1 (Complex.reCLM : ℂ → ℝ)
    exact Complex.reCLM.contDiff
  have him : ContDiff ℝ 1 (fun w : ℂ => w.im) := by
    change ContDiff ℝ 1 (Complex.imCLM : ℂ → ℝ)
    exact Complex.imCLM.contDiff
  have hn : ContDiff ℝ 1 (fun w : ℂ => Complex.normSq w) := by
    simpa only [Complex.normSq_apply] using
      (hre.mul hre).add (him.mul him)
  exact hb.mul (hn.pow (k - 1))

theorem evenWeightCutoff_hasCompactSupport
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    HasCompactSupport (evenWeightCutoff T hT k) :=
  (areaBump T hT).hasCompactSupport.mul_right

theorem evenWeightCutoff_eq_weight
    (T : ℝ) (hT : 0 ≤ T) {k : ℕ} (hk : 1 ≤ k)
    {w : ℂ} (hw : ‖w‖ ≤ T) :
    evenWeightCutoff T hT k w = ‖w‖ ^ (2 * k - 2) := by
  have hb : areaBump T hT w = 1 := by
    apply (areaBump T hT).one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_zero_right, areaBump] using
      (show ‖w‖ ≤ T + 1 by linarith)
  rw [evenWeightCutoff, hb, one_mul, Complex.normSq_eq_norm_sq]
  calc
    (‖w‖ ^ 2) ^ (k - 1) = ‖w‖ ^ (2 * (k - 1)) := by rw [pow_mul]
    _ = ‖w‖ ^ (2 * k - 2) := by congr 1; omega

theorem evenWeightCutoff_zero_of_far
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ)
    {w : ℂ} (hw : T + 2 ≤ ‖w‖) :
    evenWeightCutoff T hT k w = 0 := by
  have hb : areaBump T hT w = 0 := by
    apply (areaBump T hT).zero_of_le_dist
    simpa only [areaBump, dist_zero_right] using hw
  simp [evenWeightCutoff, hb]

/-- One bound holds for every regularized filling on the closed unit disk,
including the boundary curve used by the Stokes comparison. -/
theorem regularHarmonic_uniform_bound_closedDisk
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (s : ℝ), 0 < s → s < 1 →
        ∀ z : ℂ, ‖z‖ ≤ 1 → ‖regularHarmonic s F z‖ ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exteriorForwardGerm_bounded_unitDisk F hc
  refine ⟨1 + B, by linarith, ?_⟩
  intro s hs0 hs1 z hz
  have hsu : ‖(s : ℂ) * conj z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    have hconj : ‖conj z‖ = ‖z‖ := by
      simpa only [← Complex.star_def] using norm_star z
    rw [hconj]
    nlinarith [mul_nonneg hs0.le (norm_nonneg z)]
  calc
    ‖regularHarmonic s F z‖ ≤ ‖z‖ +
        ‖(s : ℂ) * exteriorForwardGerm F ((s : ℂ) * conj z)‖ := by
          exact norm_add_le _ _
    _ = ‖z‖ + s * ‖exteriorForwardGerm F ((s : ℂ) * conj z)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0]
    _ ≤ 1 + B := by
          have hgb := hB _ hsu
          nlinarith [mul_nonneg hs0.le (norm_nonneg
            (exteriorForwardGerm F ((s : ℂ) * conj z)))]

/-- For a regular dilate, one smooth compactly supported weight agrees with
`‖w‖^(2k-2)` on both the harmonic disk image and the actual omitted set. -/
theorem regular_evenWeightCutoff_exists
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ (T : ℝ) (hT : 0 ≤ T),
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        evenWeightCutoff T hT k (regularHarmonic s F z) =
          ‖regularHarmonic s F z‖ ^ (2 * k - 2)) ∧
      (∀ w ∈ exteriorOmitted (rescaleExterior s F),
        evenWeightCutoff T hT k w = ‖w‖ ^ (2 * k - 2)) := by
  obtain ⟨C, hC0, hC⟩ := regularHarmonic_uniform_bound_closedDisk F hc
  have hcG := rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1
  obtain ⟨M, hM0, hM⟩ :=
    exteriorOmitted_bounded (rescaleExterior s F) hcG
  let T : ℝ := max C M + 1
  have hT : 0 ≤ T := by dsimp [T]; linarith [le_max_left C M]
  refine ⟨T, hT, ?_, ?_⟩
  · intro z hz
    have hz' : ‖z‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    apply evenWeightCutoff_eq_weight T hT hk
    exact (hC s hs0 hs1 z hz').trans (by dsimp [T]; linarith [le_max_left C M])
  · intro w hw
    apply evenWeightCutoff_eq_weight T hT hk
    exact (hM w hw).trans (by dsimp [T]; linarith [le_max_right C M])

/-- A single outer source radius makes the compact weight vanish both on
the actual exterior image and on every straight segment joining that image
to the corresponding standard circle point. -/
theorem regular_evenWeightCutoff_far_outer
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    ∃ R : ℝ, 1 < R ∧
      ∀ z : ℂ, R ≤ ‖z‖ →
        evenWeightCutoff T hT k (rescaleExterior s F z) = 0 ∧
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          evenWeightCutoff T hT k
            (z + (t : ℂ) * (rescaleExterior s F z - z)) = 0 := by
  obtain ⟨C, hC0, hC⟩ := rescaleExterior_sub_id_bounded F hc hs0 hs1
  let R : ℝ := max (T + 2 + C) 1 + 1
  have hR1 : 1 < R := by dsimp [R]; linarith [le_max_right (T + 2 + C) 1]
  have hRTC : T + 2 + C ≤ R := by
    dsimp [R]
    linarith [le_max_left (T + 2 + C) 1]
  refine ⟨R, hR1, ?_⟩
  intro z hz
  constructor
  · exact rescaleExterior_compact_weight_vanish_far F hC hRTC
      (evenWeightCutoff T hT k)
      (fun w hw => evenWeightCutoff_zero_of_far T hT k hw) hz hR1
  · intro t ht0 ht1
    exact rescaleExterior_outer_homotopy_weight_vanish F hC0 hC hRTC
      (evenWeightCutoff T hT k)
      (fun w hw => evenWeightCutoff_zero_of_far T hT k hw)
      hz hR1 ht0 ht1

/-- The regularized exterior annulus term has a genuine integrable
compact-weight image formula on the actual full exterior image. -/
theorem regular_evenWeightCutoff_exteriorImage_change
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun z => ‖deriv (rescaleExterior s F) z‖ ^ 2 *
        evenWeightCutoff T hT k (rescaleExterior s F z)) exteriorDisk ∧
      (∫ w in (rescaleExterior s F) '' exteriorDisk,
        evenWeightCutoff T hT k w ∂MeasureTheory.volume) =
        ∫ z in exteriorDisk,
          ‖deriv (rescaleExterior s F) z‖ ^ 2 *
            evenWeightCutoff T hT k (rescaleExterior s F z)
          ∂MeasureTheory.volume := by
  exact exteriorImage_compact_weight_change
    (rescaleExterior s F)
    (rescaleExterior_centeredExteriorUnivalent F hc hs0 hs1)
    (evenWeightCutoff T hT k)
    (evenWeightCutoff_contDiff T hT k).continuous
    (evenWeightCutoff_hasCompactSupport T hT k)

end SpringerLean
