module
public import FourRootGluedFunctionField318
public import ActualComplexProjectiveFunctionField318
public import OpenFunctionFieldSquare318
public import Mathlib.LinearAlgebra.Dimension.Free
public section
noncomputable section
namespace FourRootActualProjectiveDegree318
open AlgebraicGeometry CategoryTheory Polynomial
open scoped nonZeroDivisors
open FourRootGluedScheme318 FourRootCoordinateOverlap318
open FourRootActualGenericField318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
abbrev Y:=ProjectiveJLine318.scheme ℂ
abbrev P:=Polynomial ℂ
local instance independentFact:Fact (QuadraticTower318.Independent (parameter b)):=⟨independent b hb⟩
local instance sourceIntegral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance affineDomain:IsDomain (Affine b):=affine_domain b hb
@[expose] def actualFinite:P→ₐ[ℂ]Affine b:=
  Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)
local instance polyAlgebra:Algebra P (Affine b):=(actualFinite b).toAlgebra
lemma actualFinite_finite:(actualFinite b).toRingHom.Finite:=by
  letI:Module.Finite P (FourRootAffineTensorPresentation318.TensorRing b):=
    (FourRootOrder318.finite_free (FourRootAffineTensorPresentation318.radicand b)).1
  letI:Module.Finite P (Affine b):=Module.Finite.equiv
    (FourRootActualFractionField318.polynomialEquivalence b).symm.toLinearEquiv
  exact RingHom.finite_algebraMap.mpr inferInstance
lemma actualFinite_injective:Function.Injective (actualFinite b):=by
  intro x y h
  have he:=congrArg (affineEmbedding b) h
  change affineEmbedding b (algebraMap P (Affine b) x)=
    affineEmbedding b (algebraMap P (Affine b) y) at he
  rw [FourRootActualFractionField318.embedding_on_polynomial,
    FourRootActualFractionField318.embedding_on_polynomial] at he
  exact (IsFractionRing.injective P K) ((algebraMap K (KummerTensorField318.Raw (parameter b))).injective he)
local instance finiteDominant:IsDominant (Spec.map (CommRingCat.ofHom (actualFinite b).toRingHom)):=
  ⟨((actualFinite_finite b).to_isIntegral.comap_surjective (actualFinite_injective b hb)).denseRange⟩
local instance chartDominant:IsDominant (finiteChart b):=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (finiteChart b).isOpenEmbedding.isOpenMap⟩

/-- Dominance is constructed from the exact ORIGINAL t chart square,
not from the shifted centered projection or degree counting. -/
theorem dominant:IsDominant (FourRootProjectiveProjection318.projection b):=by
  letI:IsDominant (finiteChart b≫FourRootProjectiveProjection318.projection b):=by
    rw [FourRootProjectiveProjection318.finite_projection]
    change IsDominant (Spec.map (CommRingCat.ofHom (actualFinite b).toRingHom)≫JLineAtlas318.chart ℂ 1)
    infer_instance
  exact IsDominant.of_comp (finiteChart b) (FourRootProjectiveProjection318.projection b)
local instance projectionDominant:IsDominant (FourRootProjectiveProjection318.projection b):=dominant b hb
local instance sourceAlgebra:Algebra (Affine b) (scheme b).functionField:=
  FourRootGluedFunctionField318.finiteAlgebra b hb
local instance targetAlgebra:Algebra P Y.functionField:=ActualComplexProjectiveFunctionField318.affineAlgebra
local instance targetFraction:IsFractionRing P Y.functionField:=
  ActualOpenFractionField318.fractionRing (JLineAtlas318.chart ℂ 1)

@[expose] def pullback:Y.functionField⟶(scheme b).functionField:=
  DominantFunctionField318.map (FourRootProjectiveProjection318.projection b)
lemma on_polynomial (p:P):pullback b hb (algebraMap P Y.functionField p)=
    algebraMap (Affine b) (scheme b).functionField (actualFinite b p):=
  OpenFunctionFieldSquare318.on_coefficient (finiteChart b) (JLineAtlas318.chart ℂ 1)
    (FourRootProjectiveProjection318.projection b) (actualFinite b).toRingHom
    (FourRootProjectiveProjection318.finite_projection b) p

/-- Exact actual generic-stalk pullback over the ORIGINAL projective t
coordinate, compared with the SAME rational coefficient embedding. -/
theorem actual_field_square:
    (FourRootGluedFunctionField318.comparison b hb).toRingHom.comp (pullback b hb).hom=
      (algebraMap K (KummerTensorField318.Raw (parameter b))).comp
        ActualComplexProjectiveFunctionField318.comparison.toRingHom:=by
  apply IsLocalization.ringHom_ext (nonZeroDivisors P)
  apply RingHom.ext
  intro p
  change FourRootGluedFunctionField318.comparison b hb
    (pullback b hb (algebraMap P Y.functionField p))=_
  rw [on_polynomial,FourRootGluedFunctionField318.on_affine]
  change affineEmbedding b (actualFinite b p)=algebraMap K _
    (ActualComplexProjectiveFunctionField318.comparison (algebraMap P Y.functionField p))
  rw [ActualComplexProjectiveFunctionField318.on_polynomial]
  exact FourRootActualFractionField318.embedding_on_polynomial b p

@[expose,instance_reducible] def pullbackAlgebra:Algebra Y.functionField (scheme b).functionField:=
  (pullback b hb).hom.toAlgebra
attribute [local instance] pullbackAlgebra
/-- Degree16 for the scalar action of the actual original projective
Scheme morphism, not an independently declared coefficient algebra. -/
theorem actual_generic_degree:Module.finrank Y.functionField (scheme b).functionField=16:=by
  have hc:(algebraMap K (KummerTensorField318.Raw (parameter b))).comp
      ActualComplexProjectiveFunctionField318.comparison.toRingHom=
      (FourRootGluedFunctionField318.comparison b hb).toRingHom.comp
        (algebraMap Y.functionField (scheme b).functionField):=
    (actual_field_square b hb).symm
  exact (Algebra.finrank_eq_of_equiv_equiv
    ActualComplexProjectiveFunctionField318.comparison.toRingEquiv
    (FourRootGluedFunctionField318.comparison b hb).toRingEquiv hc).trans
      (actual_degree b hb)
end FourRootActualProjectiveDegree318
