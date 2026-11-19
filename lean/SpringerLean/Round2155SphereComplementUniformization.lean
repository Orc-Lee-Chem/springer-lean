import SpringerLean.Round2154GridSegmentIntegral
import SpringerLean.Round2148SquareRootFromPrimitives
import SpringerLean.Round2143ReciprocalRiemannMapping

open Set Complex

namespace SpringerLean

/-- An open connected plane domain with connected spherical complement
admits primitives. Subdivide a rectilinear closed walk at the
coordinates of its vertices and apply the finite grid Cauchy theorem. -/
theorem holomorphic_isExactOn_of_sphere_compl_preconnected
    {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U)
    (hsc : IsPreconnected (((↑) : ℂ → OnePoint ℂ) '' U)ᶜ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) :
    Complex.IsExactOn f U := by
  apply RectilinearWalk.isExactOn_of_closed_integrals_eq_zero hU hc hf
  intro z p
  obtain ⟨X,Y,N,hX,hY,hgrid⟩ := p.exists_grid_coordinates
  have hcoords (w : ℂ) (hw : w ∈ p.vertices) : GridPointAtInteriorIndex X Y N w :=
    gridPointAtInteriorIndex_of_coordinates hX hY (hgrid w hw)
  obtain ⟨hbase,hbalance⟩ := p.gridCoefficients_closed_balance (X := X) (Y := Y)
  obtain ⟨hbottom,hleft,hVleft,htop,hright,hH,hV⟩ := p.gridCoefficients_support hX hY hcoords
  rw [p.integral_eq_gridIntegralPairing hX hY hf.continuousOn hcoords]
  exact gridCycle_integral_eq_zero p.trace_isCompact p.trace_subset hsc f hf X Y hX hY
    (p.gridCoefficients X Y).1 (p.gridCoefficients X Y).2 N
    hbase hbalance hbottom hleft hVleft htop hright hH hV

/-- The actual reciprocal domain of a nondegenerate compact connected
plane set is uniformized by a holomorphic disk map fixing zero. -/
theorem reciprocalDiskUniformization_exists
    (K : Set ℂ) (hK : IsCompact K) (hc : IsConnected K)
    (a b : ℂ) (ha : a ∈ continuumFill K) (hb : b ∈ continuumFill K) (hab : a ≠ b) :
    Nonempty (ReciprocalDiskUniformization K a) := by
  have hU := reciprocalExteriorDomain_isOpen K hK a
  have hconn := reciprocalExteriorDomain_isConnected K hK a ha
  have hsphere := reciprocalExteriorDomain_sphere_compl_isConnected K hK hc a ha
  exact reciprocalDiskUniformization_of_squareRootBranches K hK a b ha hb hab
    (hasHolomorphicSquareRootBranches_of_primitives hU hconn
      (holomorphic_isExactOn_of_sphere_compl_preconnected hU hconn hsphere.isPreconnected))

end SpringerLean
