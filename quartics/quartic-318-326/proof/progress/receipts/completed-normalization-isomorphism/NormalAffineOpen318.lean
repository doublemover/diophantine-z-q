module
public import IntegralGenericIso318
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public section
noncomputable section
namespace NormalAffineOpen318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsIntegralHom f] [IsDominant f]
    [IsIso (DominantFunctionField318.map f)]

theorem sections_normal (A:CommRingCat.{u}) [IsIntegrallyClosed A]
    (j:Spec A⟶Y) [IsOpenImmersion j]:IsIntegrallyClosed Γ(Y,j.opensRange):=by
  exact IsIntegrallyClosed.of_equiv
    (((Scheme.ΓSpecIso A).symm ≪≫ IsOpenImmersion.ΓIsoTop j).commRingCatIsoToRingEquiv)

/-- Restriction to the entire actual image of a normal affine chart. -/
theorem restrict_isIso (A:CommRingCat.{u}) [IsIntegrallyClosed A]
    (j:Spec A⟶Y) [IsOpenImmersion j] [Nonempty j.opensRange]:IsIso (f∣_j.opensRange):=by
  letI:=sections_normal A j
  exact IntegralGenericIso318.restrict_isIso f j.opensRange (isAffineOpen_opensRange j)
end NormalAffineOpen318
