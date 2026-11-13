module
public import ContactGeometricallyIntegral318
public import GeometricIntegralConstants318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace ContactFieldAffineChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (K : Type) [Field K] [Algebra ℚ K] (c : Fin 4 → ℚˣ)
abbrev X := ContactGlobalSmooth318.Model c
abbrev A := ContactKummerOrder318.SourceOrder c
local instance originalCommRing : CommRing (A c) := inferInstance
local instance originalAlgebra : Algebra ℚ (A c) := inferInstance
abbrev sourceStructure : X c ⟶ Spec (CommRingCat.of ℚ) :=
  ContactProjectiveModel318.modelMap c ≫ ProjectiveJLine318.structureMap ℚ
abbrev fieldMap := Spec.map (CommRingCat.ofHom (algebraMap ℚ K))
abbrev Family := pullback (fieldMap K) (sourceStructure c)
abbrev structureMap : Family K c ⟶ Spec (CommRingCat.of K) := pullback.fst _ _
abbrev chartRing := K ⊗[ℚ] A c
local instance chartCommRing : CommRing (chartRing K c) := inferInstance
local instance chartAlgebra : Algebra K (chartRing K c) := inferInstance
abbrev j := SourceGlobalAffine318.chartEmbedding c
lemma j_over : j c ≫ sourceStructure c =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (A c))) :=
  SourceGlobalAffine318.chartEmbedding_over_Q c

/-- The entire original affine chart after actual field base change. -/
def affineIso : pullback (fieldMap K) (j c ≫ sourceStructure c) ≅
    Spec (CommRingCat.of (chartRing K c)) :=
  (pullback.congrHom rfl (j_over c)) ≪≫ pullbackSpecIso ℚ K (A c)

def chart : Spec (CommRingCat.of (chartRing K c)) ⟶ Family K c :=
  (affineIso K c).inv ≫ (pullbackLeftPullbackSndIso
    (fieldMap K) (sourceStructure c) (j c)).inv ≫ pullback.fst _ _

instance chart_open : IsOpenImmersion (chart K c) := by
  unfold chart
  infer_instance

lemma chart_over : chart K c ≫ structureMap K c =
    Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K c))) := by
  simp only [chart, structureMap, Category.assoc, pullbackLeftPullbackSndIso_inv_fst]
  simp only [affineIso, Iso.trans_inv, Category.assoc, pullback.congrHom_inv,
    pullback.map, pullback.lift_fst, Category.comp_id, pullbackSpecIso_inv_fst']

instance family_proper : IsProper (structureMap K c) := by
  let : IsProper (sourceStructure c) :=
    (ContactGlobalProper318.proper_integral_extension c).2.2
  infer_instance

instance family_geometricallyIntegral : GeometricallyIntegral (structureMap K c) := by
  let : GeometricallyIntegral (sourceStructure c) :=
    ContactGeometricallyIntegral318.model_geometricallyIntegral c
  infer_instance

instance family_integral : IsIntegral (Family K c) :=
  GeometricallyIntegral.isIntegral_of_subsingleton (structureMap K c)

instance chart_domain : IsDomain (chartRing K c) := by
  let : CharZero K := algebraRat.charZero K
  exact SourceScalarExtension318.scalarExtension_domain K c

/-- The literal double scalar extension is a domain, by the actual tensor
cancellation isomorphism and the original whole source-order theorem. -/
instance chart_geometricDomain : IsDomain (AlgebraicClosure K ⊗[K] chartRing K c) := by
  let : CharZero K := algebraRat.charZero K
  let : IsScalarTower ℚ K (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : CharZero (AlgebraicClosure K) := algebraRat.charZero _
  let := SourceScalarExtension318.scalarExtension_domain (AlgebraicClosure K) c
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.cancelBaseChange ℚ K K (AlgebraicClosure K) (A c)).toRingHom
    (Algebra.TensorProduct.cancelBaseChange ℚ K K (AlgebraicClosure K) (A c)).injective
end ContactFieldAffineChart318
