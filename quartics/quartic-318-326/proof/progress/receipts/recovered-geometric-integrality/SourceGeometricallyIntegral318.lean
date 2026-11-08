module
public import SourceScalarExtension318
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace SourceGeometricallyIntegral318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
local instance integralIsoClosed :
    ObjectProperty.IsClosedUnderIsomorphisms (C:=Scheme.{u}) IsIntegral where
  of_iso e h:=by
    letI:=h
    exact IsIntegral.of_isIso e.hom
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c:Fin 4→ℚˣ)
abbrev Original:=ContactKummerOrder318.SourceOrder c
local instance originalCommRing : CommRing (Original c):=inferInstance
local instance originalAlgebra : Algebra ℚ (Original c):=inferInstance

lemma right_tensor_domain (F:Type u) [Field F] [Algebra ℚ F] :
    IsDomain (Original c⊗[ℚ]F):=by
  letI:CharZero F:=algebraRat.charZero F
  letI:=SourceScalarExtension318.scalarExtension_domain F c
  exact Function.Injective.isDomain (Algebra.TensorProduct.comm ℚ (Original c) F).toRingHom
    (Algebra.TensorProduct.comm ℚ (Original c) F).injective

/-- The structural morphism of the actual whole rational source is
geometrically integral, with the literal tensor product used at every field. -/
theorem source_geometricallyIntegral : GeometricallyIntegral
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Original c)))):=by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro F _ _
  letI:=right_tensor_domain c F
  haveI:IsIntegral (Spec (CommRingCat.of (Original c⊗[ℚ]F))):=inferInstance
  exact IsIntegral.of_isIso (pullbackSpecIso ℚ (Original c) F).inv
end SourceGeometricallyIntegral318
