import SpringerLean.Round30ActualFiniteShift

open MeasureTheory Set

namespace SpringerLean

/-- Pairing the two vertical translates converts the numerical auxiliary lower
bound into finite-window complement terms plus two compensated tails. -/
theorem compensated_integral_finite_complements_shift_pair
    (g G : ℝ → ℝ) (S E I : Set ℝ) (ε : ℝ)
    (hS : MeasurableSet S) (hE : MeasurableSet E)
    (hI : MeasurableSet I) (hES : E ⊆ S) (hIS : I ⊆ S)
    (hd : Integrable (fun t => g t - G t))
    (hgP : IntegrableOn (fun t => g (t + ε)) S)
    (hGP : IntegrableOn (fun t => G (t + ε)) S)
    (hgM : IntegrableOn (fun t => g (t - ε)) S)
    (hGM : IntegrableOn (fun t => G (t - ε)) S) :
    2 * (∫ t : ℝ, g t - G t) +
      ((∫ t in I, G (t - ε)) + (∫ t in I, G (t + ε))) -
      ((∫ t in E, g (t - ε)) + (∫ t in E, g (t + ε))) =
    ((∫ t in S \ E, g (t - ε)) + (∫ t in S \ E, g (t + ε))) -
      ((∫ t in S \ I, G (t - ε)) + (∫ t in S \ I, G (t + ε))) +
      ((∫ t in Sᶜ, g (t - ε) - G (t - ε)) +
        (∫ t in Sᶜ, g (t + ε) - G (t + ε))) := by
  have hplus := compensated_integral_finite_complements_shift
    g G S E I ε hS hE hI hES hIS hd hgP hGP
  have hminus := compensated_integral_finite_complements_shift
    g G S E I (-ε) hS hE hI hES hIS hd
      (by simpa only [sub_eq_add_neg] using hgM)
      (by simpa only [sub_eq_add_neg] using hGM)
  simp only [sub_eq_add_neg] at hplus hminus ⊢
  linarith

end SpringerLean