module
public import AffineFunctionFieldMap318
public import ActualOpenFractionField318
public section
noncomputable section
namespace OpenFunctionFieldSquare318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {R S:Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
    (jX:Spec (CommRingCat.of S)⟶X) [IsOpenImmersion jX] [IsDominant jX]
    (jY:Spec (CommRingCat.of R)⟶Y) [IsOpenImmersion jY] [IsDominant jY]
    (f:X⟶Y) [IsDominant f] (g:R→+*S) [IsDominant (Spec.map (CommRingCat.ofHom g))]
    (square:jX≫f=Spec.map (CommRingCat.ofHom g)≫jY)

local instance : Algebra R (Spec (CommRingCat.of R)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
local instance : Algebra S (Spec (CommRingCat.of S)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of S)
include square

/-- The actual generic-stalk pullbacks respect the specified affine-open
square, not merely some isomorphism of the two fields. -/
theorem map_square : DominantFunctionField318.map f≫(OpenFunctionField318.fieldIso jX).hom=
    (OpenFunctionField318.fieldIso jY).hom≫
      DominantFunctionField318.map (Spec.map (CommRingCat.ofHom g)):=by
  rw [←DominantFunctionField318.map_open,←DominantFunctionField318.map_open,
    ←DominantFunctionField318.map_comp,←DominantFunctionField318.map_comp]
  have he (a b:Spec (CommRingCat.of S)⟶Y) [IsDominant a] [IsDominant b]
      (h:a=b):DominantFunctionField318.map a=DominantFunctionField318.map b:=by
    cases h
    rfl
  exact he _ _ square

/-- Every coefficient is pulled back along exactly the affine ring map. -/
theorem on_coefficient (a:R):
    letI:=ActualOpenFractionField318.sourceAlgebra jX
    letI:=ActualOpenFractionField318.sourceAlgebra jY
    DominantFunctionField318.map f (algebraMap R Y.functionField a)=
      algebraMap S X.functionField (g a):=by
  letI:=ActualOpenFractionField318.sourceAlgebra jX
  letI:=ActualOpenFractionField318.sourceAlgebra jY
  apply (ActualOpenFractionField318.genericEquiv jX).injective
  have hs:=congrArg (fun k:Y.functionField⟶(Spec (CommRingCat.of S)).functionField=>
    k (algebraMap R Y.functionField a)) (map_square jX jY f g square)
  change (OpenFunctionField318.fieldIso jX).hom
    (DominantFunctionField318.map f (algebraMap R Y.functionField a))=
    (OpenFunctionField318.fieldIso jX).hom (algebraMap S X.functionField (g a))
  rw [show (OpenFunctionField318.fieldIso jX).hom
      (algebraMap S X.functionField (g a))=algebraMap S (Spec (CommRingCat.of S)).functionField (g a)
      from (ActualOpenFractionField318.genericAlgEquiv jX).commutes (g a)]
  exact hs.trans ((congrArg (DominantFunctionField318.map (Spec.map (CommRingCat.ofHom g)))
    ((ActualOpenFractionField318.genericAlgEquiv jY).commutes a)).trans
      (AffineFunctionFieldMap318.on_coefficient g a))
end OpenFunctionFieldSquare318
