module
public import SheafInverseImageConstants318
public import Mathlib.AlgebraicGeometry.OpenImmersion

public section
noncomputable section
namespace OpenImmersionAdditiveRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Original restriction along an open immersion, evaluated on actual image opens. -/
abbrev restriction := f.isOpenEmbedding.sheafPullback AddCommGrpCat.{0}

instance restriction_limits : PreservesFiniteLimits (restriction f) := by
  let e : SheafInverseImageConstants318.inverseImage f.base ≅ restriction f :=
    f.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{0}
  let := SheafInverseImageConstants318.inverseImage_limits f.base
  exact preservesFiniteLimits_of_natIso e
instance restriction_colimits : PreservesFiniteColimits (restriction f) := by
  let e : SheafInverseImageConstants318.inverseImage f.base ≅ restriction f :=
    f.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{0}
  let := SheafInverseImageConstants318.inverseImage_colimits f.base
  exact preservesFiniteColimits_of_natIso e
instance restriction_additive : (restriction f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The actual ring-section isomorphisms of the open immersion, with multiplication forgotten. -/
@[expose] def structureIso : (restriction f).obj (StructureAdditiveSheaf318.sheaf Y) ≅
    StructureAdditiveSheaf318.sheaf X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun U => StructureAdditiveSheaf318.additiveForget.mapIso
      (f.appIso U.unop)) (by
        intro U V i
        exact congrArg (StructureAdditiveSheaf318.additiveForget.map)
          (f.appIso_hom_naturality i)))

theorem structureIso_hom_app (U : X.Opens) (s : Γ(Y,f ''ᵁ U)) :
    (structureIso f).hom.hom.app (op U) s = (f.appIso U).hom s := rfl

end OpenImmersionAdditiveRestriction318
