module
public import OriginalPointFinitePlaceRoots318
public section
noncomputable section
namespace OriginalPointFinitePlaceCenter318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (v : FinitePlace (K c t))
  (hv : v (denominator c:K c t)=1)
@[expose] def center : Spec (CommRingCat.of (V c t v)) ⟶
    IntegralGluedModel318.scheme (V c t v) (localTwists c t v hv) :=
  IntegralValuativePointCenter318.center (V c t v) (K c t) (localTwists c t v hv)
    (t:K c t) (roots c t) (local_root_equations c t v hv)

/-- The actual point field's finite-place center extends its specified
original signed-root point, without a caller-supplied extension premise. -/
theorem generic_specialization :
    Spec.map (CommRingCat.ofHom (algebraMap (V c t v) (K c t))) ≫ center c t v hv=
      IntegralValuativeGenericPoint318.point (V c t v) (K c t) (localTwists c t v hv)
        (t:K c t) (roots c t) (local_root_equations c t v hv) :=
  IntegralValuativePointCenter318.center_generic _ _ _ _ _ _

theorem over_base : center c t v hv ≫
    IntegralGluedModel318.structureMap (V c t v) (localTwists c t v hv)=𝟙 _ :=
  IntegralValuativePointCenter318.center_over_base _ _ _ _ _ _

/-- At an integral t the full original finite cover supplies a contact
chart and its entire ring map, retaining every original source value. -/
theorem branch_center (ht : IsLocalization.IsInteger (V c t v) (t:K c t)) :
    ∃ (i : Fin 4) (f : IntegralBranchCoordinates318.B (V c t v) (localTwists c t v hv) i →+* V c t v),
      (∀ a : IntegralSourceBranches318.SourceOrder (V c t v) (localTwists c t v hv),
        algebraMap (V c t v) (K c t) (f (algebraMap _ _ a))=
          IntegralValuativeGenericPoint318.sourceMap (V c t v) (K c t) (localTwists c t v hv)
            (t:K c t) (roots c t) (local_root_equations c t v hv) a) ∧
      algebraMap (V c t v) (K c t) (f (IntegralBranchCoordinates318.sourceCoordinate
        (V c t v) (localTwists c t v hv) i))=roots c t i :=
  IntegralValuativePointCenter318.finite_branch_center _ _ _ _ _ _
    (ContactFinitePlaceBaseMap318.separation_unit c v hv) ht
end OriginalPointFinitePlaceCenter318
