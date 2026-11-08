module
public import DominantFunctionField318
public section
noncomputable section
namespace AffineFunctionFieldMap318
open CategoryTheory AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (g:R→+*S) [IsDominant (Spec.map (CommRingCat.ofHom g))]
local instance : Algebra R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
local instance : Algebra S (Spec (CommRingCat.of S)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of S)

/-- Pullback on actual affine generic stalks preserves precisely the given
coordinate-ring homomorphism. -/
theorem on_coefficients :
    CommRingCat.ofHom (algebraMap R (Spec (CommRingCat.of R)).functionField)≫
      DominantFunctionField318.map (Spec.map (CommRingCat.ofHom g))=
    CommRingCat.ofHom g≫CommRingCat.ofHom (algebraMap S (Spec (CommRingCat.of S)).functionField):=by
  change StructureSheaf.toStalk R (genericPoint (Spec (CommRingCat.of R)))≫
    ((Spec (CommRingCat.of R)).presheaf.stalkCongr _).inv≫
      (Spec.map (CommRingCat.ofHom g)).stalkMap (genericPoint (Spec (CommRingCat.of S)))=_
  rw [←Category.assoc,TopCat.Presheaf.stalkCongr_inv]
  erw [StructureSheaf.toStalk_stalkSpecializes]
  exact stalkMap_toStalk (CommRingCat.ofHom g) _

theorem on_coefficient (a:R):
    DominantFunctionField318.map (Spec.map (CommRingCat.ofHom g))
      (algebraMap R (Spec (CommRingCat.of R)).functionField a)=
    algebraMap S (Spec (CommRingCat.of S)).functionField (g a):=
  congrArg (fun f:CommRingCat.of R⟶(Spec (CommRingCat.of S)).functionField=>f a) (on_coefficients g)
end AffineFunctionFieldMap318
