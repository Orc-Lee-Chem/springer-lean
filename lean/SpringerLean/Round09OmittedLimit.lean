import SpringerLean.Round09OmittedScale

open MeasureTheory Filter
open scoped Topology

namespace SpringerLean

/-- A concrete increasing sequence of regularization parameters, starting
at `1/2` and approaching one from below. -/
noncomputable def omittedScaleSeq (n : ℕ) : ℝ := ((n : ℝ) + 1) / ((n : ℝ) + 2)

theorem omittedScaleSeq_pos (n : ℕ) : 0 < omittedScaleSeq n := by
  unfold omittedScaleSeq
  positivity

theorem omittedScaleSeq_lt_one (n : ℕ) : omittedScaleSeq n < 1 := by
  unfold omittedScaleSeq
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
  linarith

theorem omittedScaleSeq_mono : Monotone omittedScaleSeq := by
  intro i j hij
  unfold omittedScaleSeq
  have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  have hj : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  apply (div_le_div_iff₀ hi hj).mpr
  nlinarith

theorem omittedScaleSeq_tendsto_one :
    Tendsto omittedScaleSeq atTop (𝓝 (1 : ℝ)) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hfun :
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) =
        omittedScaleSeq := by
    funext n
    simp only [omittedScaleSeq, Nat.cast_add, Nat.cast_one]
    ring
  simpa only [Function.comp_def, hfun] using h

/-- The actual omitted set is the intersection along this explicit cofinal
sequence. This is stronger than merely recording the pointwise filter limit. -/
theorem exteriorOmitted_eq_iInter_scaleSeq (F : ℂ → ℂ) :
    (⋂ n : ℕ, exteriorOmittedAtScale F (omittedScaleSeq n)) =
      exteriorOmitted F := by
  ext w
  simp only [Set.mem_iInter]
  constructor
  · intro hall
    apply (exteriorOmitted_iff_all_scales F w).mpr
    intro s hs0 hs1
    obtain ⟨n, hn⟩ :=
      ((omittedScaleSeq_tendsto_one.eventually (lt_mem_nhds hs1)).exists)
    exact exteriorOmittedAtScale_antitone F hs0 hn.le (hall n)
  · intro hw n
    exact (exteriorOmitted_iff_all_scales F w).mp hw
      (omittedScaleSeq n) (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)

/-- Continuity from above of the actual weighted omitted-area integrals
along the concrete regularization sequence. -/
theorem exteriorOmittedAtScale_weighted_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    Tendsto
      (fun n : ℕ => ∫ w in exteriorOmittedAtScale F (omittedScaleSeq n),
        ‖w‖ ^ m ∂volume)
      atTop
      (𝓝 (∫ w in exteriorOmitted F, ‖w‖ ^ m ∂volume)) := by
  let K : ℕ → Set ℂ := fun n => exteriorOmittedAtScale F (omittedScaleSeq n)
  have hmeas : ∀ n, MeasurableSet (K n) := by
    intro n
    exact exteriorOmittedAtScale_measurableSet F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n)
  have hanti : Antitone K := by
    intro i j hij
    exact exteriorOmittedAtScale_antitone F
      (omittedScaleSeq_pos i) (omittedScaleSeq_mono hij)
  have hint : ∃ n, IntegrableOn (fun w : ℂ => ‖w‖ ^ m) (K n) := by
    refine ⟨0, ?_⟩
    exact exteriorOmittedAtScale_weight_integrableOn F hc
      (omittedScaleSeq_pos 0) (omittedScaleSeq_lt_one 0) m
  have hlim := tendsto_setIntegral_of_antitone hmeas hanti hint
  simpa only [K, exteriorOmitted_eq_iInter_scaleSeq F] using hlim

/-- The genuine omitted-set weighted area of the regular dilates converges
to that of the original map along a common explicit approximation sequence. -/
theorem rescaleExterior_omitted_weighted_integral_tendsto
    (F : ℂ → ℂ) (hc : CenteredExteriorUnivalent F) (m : ℕ) :
    Tendsto
      (fun n : ℕ => ∫ w in exteriorOmitted
          (rescaleExterior (omittedScaleSeq n) F),
        ‖w‖ ^ m ∂volume)
      atTop
      (𝓝 (∫ w in exteriorOmitted F, ‖w‖ ^ m ∂volume)) := by
  have hfun :
      (fun n : ℕ => ∫ w in exteriorOmitted
          (rescaleExterior (omittedScaleSeq n) F), ‖w‖ ^ m ∂volume) =
      (fun n : ℕ => omittedScaleSeq n ^ (m + 2) *
        (∫ w in exteriorOmittedAtScale F (omittedScaleSeq n),
          ‖w‖ ^ m ∂volume)) := by
    funext n
    exact rescaleExterior_omitted_weighted_integral F hc
      (omittedScaleSeq_pos n) (omittedScaleSeq_lt_one n) m
  rw [hfun]
  have hlim := (omittedScaleSeq_tendsto_one.pow (m + 2)).mul
    (exteriorOmittedAtScale_weighted_integral_tendsto F hc m)
  simpa only [one_pow, one_mul] using hlim

end SpringerLean
