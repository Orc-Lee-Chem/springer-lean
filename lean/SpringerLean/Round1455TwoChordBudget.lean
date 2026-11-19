import SpringerLean.Round1454ActualTwoChordCost

namespace SpringerLean

/-- The two positive moving-chord savings are removed from the SAME
two-circle model budget. No actual function is used in this scalar
integration statement. -/
theorem refinedAffine_two_moving_chords_budget
    (n : ℕ) (hn : 1501 ≤ n)
    {W₁ W₂ d₁ d₂ : ℝ}
    (hW₁0 : 0 ≤ W₁) (hW₁ : W₁ ≤ 1/500)
    (hW₁sq : (n:ℝ)*W₁^2 ≤ 3/500)
    (hW₂0 : 0 ≤ W₂) (hW₂ : W₂ ≤ 1/500)
    (hW₂sq : (n:ℝ)*W₂^2 ≤ 3/500)
    (hd₁ : 0 < d₁) (hnd₁ : (n:ℝ)*d₁ < 1)
    (hd₂ : 0 < d₂) (hnd₂ : (n:ℝ)*d₂ < 1) :
    let I : ℝ := Real.circleAverage
      (fun ζ : ℂ => |2*ζ.re|^n) 0 1
    let b₁ : ℝ := Real.sqrt (3*d₁)
    let b₂ : ℝ := Real.sqrt (3*d₂)
    let T₁ : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W₁ n
        (2*Real.cos b₁) (2*Real.sin b₁/b₁) (2*ζ.re)) 0 1
    let T₂ : ℝ := Real.circleAverage
      (fun ζ : ℂ => refinedAffineChordPower W₂ n
        (2*Real.cos b₂) (2*Real.sin b₂/b₂) (2*ζ.re)) 0 1
    let S₁ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₁)^2*
      Real.sqrt ((n:ℝ)*d₁)*Real.exp (-(61/100:ℝ)*((n:ℝ)*d₁))
    let S₂ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₂)^2*
      Real.sqrt ((n:ℝ)*d₂)*Real.exp (-(61/100:ℝ)*((n:ℝ)*d₂))
    T₁+T₂+S₁+S₂ <
      2*(19/10:ℝ)^n+(I/2)*
        (2+(57/100:ℝ)*(W₁+W₂)+
          (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2)) := by
  dsimp
  let I : ℝ := Real.circleAverage
    (fun ζ : ℂ => |2*ζ.re|^n) 0 1
  let V₁ : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineRadius W₁ (2*ζ.re)^n) 0 1
  let V₂ : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineRadius W₂ (2*ζ.re)^n) 0 1
  let b₁ : ℝ := Real.sqrt (3*d₁)
  let b₂ : ℝ := Real.sqrt (3*d₂)
  let T₁ : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineChordPower W₁ n
      (2*Real.cos b₁) (2*Real.sin b₁/b₁) (2*ζ.re)) 0 1
  let T₂ : ℝ := Real.circleAverage
    (fun ζ : ℂ => refinedAffineChordPower W₂ n
      (2*Real.cos b₂) (2*Real.sin b₂/b₂) (2*ζ.re)) 0 1
  let S₁ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₁)^2*
    Real.sqrt ((n:ℝ)*d₁)*Real.exp (-(61/100:ℝ)*((n:ℝ)*d₁))
  let S₂ : ℝ := (67/1000:ℝ)*I*((n:ℝ)*d₂)^2*
    Real.sqrt ((n:ℝ)*d₂)*Real.exp (-(61/100:ℝ)*((n:ℝ)*d₂))
  have hsave₁ := refinedAffineChord_moving_saving_0067
    n hn hW₁0 hW₁ hd₁ hnd₁
  have hsave₂ := refinedAffineChord_moving_saving_0067
    n hn hW₂0 hW₂ hd₂ hnd₂
  change S₁ < V₁-T₁ at hsave₁
  change S₂ < V₂-T₂ at hsave₂
  have hV₁ := refinedAffineModelCircle_le n hW₁0 hW₁ hW₁sq
  have hV₂ := refinedAffineModelCircle_le n hW₂0 hW₂ hW₂sq
  change V₁ ≤ (19/10:ℝ)^n+(I/2)*
    (1+(57/100:ℝ)*W₁+(55/100:ℝ)*(n:ℝ)*W₁^2) at hV₁
  change V₂ ≤ (19/10:ℝ)^n+(I/2)*
    (1+(57/100:ℝ)*W₂+(55/100:ℝ)*(n:ℝ)*W₂^2) at hV₂
  have hsave : T₁+T₂+S₁+S₂ < V₁+V₂ := by
    linarith [hsave₁,hsave₂]
  have hbudget : V₁+V₂ ≤
      2*(19/10:ℝ)^n+(I/2)*
        (2+(57/100:ℝ)*(W₁+W₂)+
          (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2)) := by
    have hh := add_le_add hV₁ hV₂
    convert hh using 1 <;> ring
  change T₁+T₂+S₁+S₂ <
    2*(19/10:ℝ)^n+(I/2)*
      (2+(57/100:ℝ)*(W₁+W₂)+
        (55/100:ℝ)*(n:ℝ)*(W₁^2+W₂^2))
  exact hsave.trans_le hbudget

end SpringerLean

#print axioms SpringerLean.refinedAffine_two_moving_chords_budget
