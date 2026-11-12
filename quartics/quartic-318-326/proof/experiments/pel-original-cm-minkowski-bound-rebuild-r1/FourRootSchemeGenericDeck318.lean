module
public import FourRootGluedFunctionField318
public import FourRootSchemeSignAction318
public import OpenFunctionFieldSquare318
public section
noncomputable section
namespace FourRootSchemeGenericDeck318
open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors
open FourRootGluedScheme318 FourRootCoordinateOverlap318
open FourRootSchemeSignAction318 FourRootGluedFunctionField318
open FourRootActualGenericField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b) (g:FourBinaryCharacters318.Group)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance sourceIntegral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance affineDomain:IsDomain (Affine b):=affine_domain b hb
local instance sourceAlgebra:Algebra (Affine b) (scheme b).functionField:=finiteAlgebra b hb
local instance sourceFraction:IsFractionRing (Affine b) (scheme b).functionField:=
  ActualOpenFractionField318.fractionRing (finiteChart b)
local instance chartDominant:IsDominant (finiteChart b):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (finiteChart b).isOpenEmbedding.isOpenMap⟩
local instance actionIso:IsIso (action b g):=by
  change IsIso (schemeIso b g).hom
  infer_instance
local instance finiteIso:IsIso (finiteMap b g):=by
  let e:finiteScheme b≅finiteScheme b:=
    ⟨finiteMap b g,finiteMap b g,finiteMap_square b g,finiteMap_square b g⟩
  change IsIso e.hom
  infer_instance

/-- The pullback is the ACTUAL generic-stalk map of the glued Scheme
sign automorphism, with its original finite-chart square. -/
lemma on_affine (x:Affine b):DominantFunctionField318.map (action b g)
    (algebraMap (Affine b) (scheme b).functionField x)=
    algebraMap (Affine b) (scheme b).functionField
      (FourRootCoordinateRingSigns318.finiteEnd b g x):=
  OpenFunctionFieldSquare318.on_coefficient (finiteChart b) (finiteChart b)
    (action b g) (FourRootCoordinateRingSigns318.finiteEnd b g).toRingHom
    (finite_action b g) x

/-- The whole actual Scheme generic-stalk action is EXACTLY the same
root-sign automorphism of its identified sixteen-degree field. Equality
on the affine coefficients determines the entire genuine fraction field. -/
theorem equivariant (z:(scheme b).functionField):
    comparison b hb (DominantFunctionField318.map (action b g) z)=
      FourRootActualGenericSigns318.genericAutomorphism b g (comparison b hb z):=by
  have he:(comparison b hb).toRingHom.comp
      (DominantFunctionField318.map (action b g)).hom=
      (FourRootActualGenericSigns318.genericAutomorphism b g).toRingHom.comp
        (comparison b hb).toRingHom:=by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Affine b))
    apply RingHom.ext
    intro x
    change comparison b hb (DominantFunctionField318.map (action b g)
      (algebraMap (Affine b) (scheme b).functionField x))=_
    rw [on_affine,FourRootGluedFunctionField318.on_affine,
      FourRootGluedFunctionField318.on_affine]
    exact FourRootActualGenericSigns318.affineEmbedding_equivariant b g x
  exact RingHom.congr_fun he z
end FourRootSchemeGenericDeck318
