import SpringerLean.Round1415CandidateTwoAffineCaps

namespace SpringerLean

/-- The final projection test is a positive plateau above one affine
function. Its parameter is the squared root-strip width. -/
noncomputable def refinedAffineRadius (W x : ℝ) : ℝ :=
  max (19/10 : ℝ)
    (2-(1-(107/100 : ℝ)*W)*(2-x)+(107/100 : ℝ)*W^2)

theorem refinedAffineRadius_pos (W x : ℝ) :
    0 < refinedAffineRadius W x := by
  unfold refinedAffineRadius
  exact (by norm_num : (0 : ℝ) < 19/10).trans_le (le_max_left _ _)

/-- No monotonicity assumption on W is needed for convexity: the
nonconstant branch is affine for every fixed W. -/
theorem refinedAffineRadius_pow_convexOn (W : ℝ) (n : ℕ) :
    ConvexOn ℝ Set.univ (fun x : ℝ => refinedAffineRadius W x ^ n) := by
  have haff : ConvexOn ℝ Set.univ
      (fun x : ℝ =>
        2-(1-(107/100 : ℝ)*W)*(2-x)+(107/100 : ℝ)*W^2) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    apply le_of_eq
    calc
      2-(1-(107/100 : ℝ)*W)*(2-(a*x+b*y))+(107/100 : ℝ)*W^2 =
          (a+b)*(2-2*(1-(107/100 : ℝ)*W)+(107/100 : ℝ)*W^2)+
            (1-(107/100 : ℝ)*W)*(a*x+b*y) := by rw [hab]; ring
      _ = a*(2-(1-(107/100 : ℝ)*W)*(2-x)+(107/100 : ℝ)*W^2)+
          b*(2-(1-(107/100 : ℝ)*W)*(2-y)+(107/100 : ℝ)*W^2) := by ring
  have hmax : ConvexOn ℝ Set.univ (refinedAffineRadius W) := by
    unfold refinedAffineRadius
    convert (convexOn_const (19/10 : ℝ) convex_univ).sup haff using 1
  convert (hmax.pow (fun x _ =>
    (refinedAffineRadius_pos W x).le) n) using 1

end SpringerLean

#print axioms SpringerLean.refinedAffineRadius_pow_convexOn
