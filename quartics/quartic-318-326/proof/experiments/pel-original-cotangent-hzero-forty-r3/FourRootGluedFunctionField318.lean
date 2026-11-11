module
public import FourRootWholeSchemeGeometry318
public import FourRootActualFractionField318
public import ActualOpenFractionField318
public section
noncomputable section
namespace FourRootGluedFunctionField318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootCoordinateOverlap318
open FourRootActualGenericField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance sourceIntegral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance affineDomain:IsDomain (Affine b):=affine_domain b hb
abbrev L:=KummerTensorField318.Raw (parameter b)
local instance rawAlgebra:Algebra (Affine b) (L b):=(affineEmbedding b).toAlgebra
local instance rawFraction:IsFractionRing (Affine b) (L b):=
  FourRootActualFractionField318.actual_fractionField b hb

/-- The coefficient map is the actual generic-stalk map of the original
finite chart, as defined by its genuine open immersion. -/
@[expose,instance_reducible] def finiteAlgebra:Algebra (Affine b) (scheme b).functionField:=
  ActualOpenFractionField318.sourceAlgebra (finiteChart b)
attribute [local instance] finiteAlgebra

/-- The function field of the WHOLE independently glued contact Scheme
is the SAME sixteen-degree root field, preserving actual affine germs. -/
@[expose] def comparison:(scheme b).functionField≃ₐ[Affine b]L b:=
  ActualOpenFractionField318.equiv (finiteChart b) (L b)

theorem on_affine (x:Affine b):
    comparison b hb (algebraMap (Affine b) (scheme b).functionField x)=affineEmbedding b x:=
  (comparison b hb).commutes x

theorem on_root (i:Fin 4):comparison b hb
    (algebraMap (Affine b) (scheme b).functionField
      (FourRootAffineCoordinateRing318.coordinate b (some i)))=
    FourRootAutomorphisms318.generator (parameter b) i:=by
  rw [on_affine]
  exact FourRootActualCharacterFields318.affine_root b i

/-- The rational-function coefficient field acts through the SAME full
field identification. The finite polynomial coefficient germs below
remain explicit, so no unrelated base coordinate can be substituted. -/
@[expose,instance_reducible] def rationalAlgebra:Algebra K (scheme b).functionField:=
  ((comparison b hb).symm.toRingHom.comp (algebraMap K (L b))).toAlgebra

@[expose] def rationalComparison:
    letI:=rationalAlgebra b hb
    (scheme b).functionField≃ₐ[K]L b:=by
  letI:=rationalAlgebra b hb
  exact {(comparison b hb).toRingEquiv with
    commutes':=by intro x;exact (comparison b hb).apply_symm_apply _}

lemma on_original_t:comparison b hb
    (algebraMap (Affine b) (scheme b).functionField
      (FourRootAffineCoordinateRing318.coordinate b none))=
    algebraMap K (L b) (algebraMap (Polynomial ℂ) K Polynomial.X):=by
  rw [on_affine]
  have h:=FourRootActualFractionField318.embedding_on_polynomial b Polynomial.X
  change affineEmbedding b
    ((Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)) Polynomial.X)=_ at h
  simpa only [Polynomial.aeval_X] using h

lemma original_root_germ (i:Fin 4):
    (comparison b hb).symm (FourRootAutomorphisms318.generator (parameter b) i)=
      algebraMap (Affine b) (scheme b).functionField
        (FourRootAffineCoordinateRing318.coordinate b (some i)):=by
  apply (comparison b hb).injective
  rw [AlgEquiv.apply_symm_apply,on_root]
end FourRootGluedFunctionField318
