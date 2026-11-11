module
public import ReducedSchemePointFactorization318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace ReducedClosedChartComparison318
open AlgebraicGeometry CategoryTheory
variable {X Y Z:Scheme}(i:X⟶Z)(j:Y⟶Z)
  [IsClosedImmersion i][IsClosedImmersion j][IsReduced X][IsReduced Y]
lemma actual_kernel_eq(h:Set.range i=Set.range j):i.ker=j.ker:=by
  have hs:i.ker.support=j.ker.support:=by
    apply SetLike.coe_injective
    rw [i.support_ker,j.support_ker,h]
  calc
    i.ker=Scheme.IdealSheafData.vanishingIdeal i.ker.support:=by
      rw [Scheme.IdealSheafData.vanishingIdeal_support,
        ReducedSchemePointFactorization318.kernel_radical]
    _=Scheme.IdealSheafData.vanishingIdeal j.ker.support:=congrArg _ hs
    _=j.ker:=by
      rw [Scheme.IdealSheafData.vanishingIdeal_support,
        ReducedSchemePointFactorization318.kernel_radical]
/-- Two genuine reduced closed subschemes with the same FULL support
are isomorphic through their actual ideal sheaves, over the original
ambient Scheme. This is not a comparison only on complex points. -/
@[expose] def comparison(h:Set.range i=Set.range j):X≅Y:=by
  let f:=IsClosedImmersion.lift j i (actual_kernel_eq i j h).ge
  haveI:IsIso f:=IsClosedImmersion.isIso_lift j i (actual_kernel_eq i j h).symm
  exact asIso f
@[reassoc] lemma comparison_over(h:Set.range i=Set.range j):
    (comparison i j h).hom≫j=i:=by
  exact IsClosedImmersion.lift_fac j i (actual_kernel_eq i j h).ge
end ReducedClosedChartComparison318
