import SpringerLean.Round1590ActualDriftReduction

namespace SpringerLean

/-- The second-derivative cancellation for a harmonic filling
`H(z)=z+g(conj z)`: the derivative of `c=g'(conj z)` appears in
both Cartesian second derivatives with opposite signs. -/
theorem phase_laplacian_coordinate_algebra (A W c d : ℂ) :
    (A*(1+c)^2+W*d).im +
      (A*Complex.I*(1-c)^2+W*Complex.I*d).re =
    4*(A*c).im := by
  rcases A with ⟨a,b⟩
  rcases W with ⟨u,v⟩
  rcases c with ⟨p,q⟩
  rcases d with ⟨e,f⟩
  simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, pow_two]
  ring

end SpringerLean

#print axioms SpringerLean.phase_laplacian_coordinate_algebra
