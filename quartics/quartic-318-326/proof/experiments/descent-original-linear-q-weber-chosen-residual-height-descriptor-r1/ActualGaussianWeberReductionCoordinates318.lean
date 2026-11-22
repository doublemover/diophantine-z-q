module
public import ActualGaussianWeberHenselianPointMap318
public section
noncomputable section

namespace ActualGaussianWeberReductionCoordinates318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318

variable {F : Type*} [Field F] (V : ValuationSubring F)

private theorem transport_some {K : Type*} [CommRing K] {x y x' y' : K}
    {h : (curve K).toAffine.Nonsingular x y}
    {h' : (curve K).toAffine.Nonsingular x' y'} (hx : x=x') (hy : y=y') :
    Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

/-- The actual finite reduction read through its integral coordinates.
The membership proofs inside the stock constructor are not reindexed by rw. -/
theorem reduction_through_coordinates (h2 : (2:ResidueField V) ≠ 0)
    {x y : F} (hn : WeierstrassCurve.Affine.Nonsingular ((curve F).toAffine) x y) (a b : V)
    (hx : x=V.subtype a) (hy : y=V.subtype b) :
    ∃ h : WeierstrassCurve.Affine.Nonsingular ((curve (ResidueField V)).toAffine) (residue V a) (residue V b),
      specialize V h2 (Point.some x y hn)=Point.some (residue V a) (residue V b) h := by
  subst x
  subst y
  classical
  have hQ := (literal_equation _ _).mp hn.1
  have hV := equation_in_subring V a b hQ
  refine ⟨nonsing_of_equation h2 (equation_in_residue V a b hV),?_⟩
  have ha : V.subtype a ∈ V := a.property
  have ea : (⟨V.subtype a,ha⟩ : V)=a := Subtype.ext rfl
  have eb : (⟨V.subtype b,integral_y V hQ ha⟩ : V)=b := Subtype.ext rfl
  simp only [specialize,dif_pos ha,finiteReduction]
  exact transport_some (congrArg (residue V) ea) (congrArg (residue V) eb)

end ActualGaussianWeberReductionCoordinates318
