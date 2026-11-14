module
public import FourRootActualMeromorphicFrames318
public import FourRootGluedScheme318
public import IntrinsicChartFrames318
public section
noncomputable section
namespace FourRootIntrinsicCanonicalFrames318
open AlgebraicGeometry CategoryTheory Opposite
open FourRootGluedScheme318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
/-- The actual universal intrinsic differential SHEAF on the unchanged
whole normalized contact Scheme. No coefficient-divisor sheaf is
substituted for this object. -/
@[expose] def omega:(scheme b).Modules:=FamilyIntrinsicDifferentials318.omega (structureMap b)
abbrev FiniteRing(i:Fin 4):=FourRootActualBranchKaehler318.SourceRing b i
abbrev InfinityRing:=FourRootActualInfinityKaehler318.SourceRing b hb
@[expose] def finiteEmbedding(i:Fin 4):Spec (CommRingCat.of (FiniteRing b i))⟶scheme b:=
  Spec.map (CommRingCat.ofHom (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i)))≫finiteChart b
instance finiteEmbedding_open(i:Fin 4):IsOpenImmersion (finiteEmbedding b i):=by
  haveI:IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i)))):=
    IsOpenImmersion.of_isLocalization (FourRootActualFiniteBranchChart318.denominator b i)
  unfold finiteEmbedding
  infer_instance
lemma finite_structure(i:Fin 4):finiteEmbedding b i≫structureMap b=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (FiniteRing b i))):=by
  rw [finiteEmbedding,Category.assoc,FourRootGluedScheme318.finite_structure]
  unfold finiteBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply ℂ (FourRootAffineCoordinateRing318.Ring b) (FiniteRing b i) c).symm
@[expose] def infinityEmbedding:Spec (CommRingCat.of (InfinityRing b hb))⟶scheme b:=
  Spec.map (CommRingCat.ofHom (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb)))≫infinityChart b
instance infinityEmbedding_open:IsOpenImmersion (infinityEmbedding b hb):=by
  haveI:IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb)))):=
    IsOpenImmersion.of_isLocalization (FourRootActualInfinityKaehler318.denominator b hb)
  unfold infinityEmbedding
  infer_instance
lemma infinity_structure:infinityEmbedding b hb≫structureMap b=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (InfinityRing b hb))):=by
  rw [infinityEmbedding,Category.assoc,FourRootGluedScheme318.infinity_structure]
  unfold infinityBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply ℂ (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb) c).symm

/-- Genuine local O-module isomorphisms for the actual whole intrinsic
Omega, produced by its universal derivation comparison. -/
@[expose] def finiteFrame(i:Fin 4):
    (Scheme.Modules.restrictFunctor (finiteEmbedding b i)).obj (SheafOfModules.unit (scheme b).ringCatSheaf)≅
      (omega b).restrict (finiteEmbedding b i):=
  IntrinsicChartFrames318.frame (finiteEmbedding b i) (structureMap b) (finite_structure b i)
    (FourRootActualBranchKaehler318.sourceFrame b i)
@[expose] def infinityFrame:
    (Scheme.Modules.restrictFunctor (infinityEmbedding b hb)).obj (SheafOfModules.unit (scheme b).ringCatSheaf)≅
      (omega b).restrict (infinityEmbedding b hb):=
  IntrinsicChartFrames318.frame (infinityEmbedding b hb) (structureMap b) (infinity_structure b hb)
    (FourRootActualInfinityKaehler318.frame b hb)
@[expose] def finiteGenerator(i:Fin 4):Γ(omega b,finiteEmbedding b i ''ᵁ ⊤):=
  IntrinsicChartSections318.sectionMap (finiteEmbedding b i) (structureMap b) (finite_structure b i)
    (KaehlerDifferential.D ℂ (FiniteRing b i) (FourRootActualBranchKaehler318.sourceCoordinate b i))
@[expose] def infinityGenerator:Γ(omega b,infinityEmbedding b hb ''ᵁ ⊤):=
  IntrinsicChartSections318.sectionMap (infinityEmbedding b hb) (structureMap b) (infinity_structure b hb)
    (KaehlerDifferential.D ℂ (InfinityRing b hb) (FourRootActualInfinityKaehler318.coordinate b hb))
theorem finiteFrame_one(i:Fin 4):(finiteFrame b i).hom.val.app (op ⊤) (show Γ(scheme b,finiteEmbedding b i ''ᵁ ⊤) from 1)=
    finiteGenerator b i:=
  IntrinsicChartFrames318.frame_one (finiteEmbedding b i) (structureMap b) (finite_structure b i)
    (FourRootActualBranchKaehler318.sourceFrame b i) _ (FourRootActualBranchKaehler318.source_normalized b i)
theorem infinityFrame_one:(infinityFrame b hb).hom.val.app (op ⊤)
    (show Γ(scheme b,infinityEmbedding b hb ''ᵁ ⊤) from 1)=infinityGenerator b hb:=
  IntrinsicChartFrames318.frame_one (infinityEmbedding b hb) (structureMap b) (infinity_structure b hb)
    (FourRootActualInfinityKaehler318.frame b hb) _ (FourRootActualInfinityKaehler318.coordinate_normalized b hb)
/-- Actual original dt as an intrinsic sheaf section is exactly the
literal signed-root multiple of the genuine local Omega generator. -/
theorem finite_original_dt(i:Fin 4):
    (FamilyIntrinsicDifferentials318.D (structureMap b)).d
      (((finiteEmbedding b i).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
          (FourRootActualBranchKaehler318.sourceParameter b i)))=
    (((finiteEmbedding b i).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
        (2*FourRootActualBranchKaehler318.sourceCoordinate b i))) • finiteGenerator b i:=by
  rw [←IntrinsicChartSections318.section_D,
    FourRootActualBranchKaehler318.parameter_differential,
    IntrinsicChartSections318.section_smul]
  rfl
/-- The infinity intrinsic sheaf identity uses dv for v=u². The original
dt has its separately proved pole of order three in this same u frame. -/
theorem infinity_reciprocal_dv:
    (FamilyIntrinsicDifferentials318.D (structureMap b)).d
      (((infinityEmbedding b hb).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of (InfinityRing b hb))).inv
          (FourRootActualInfinityKaehler318.reciprocalParameter b hb)))=
    (((infinityEmbedding b hb).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (InfinityRing b hb))).inv
        (2*FourRootActualInfinityKaehler318.coordinate b hb))) • infinityGenerator b hb:=by
  rw [←IntrinsicChartSections318.section_D,
    FourRootActualInfinityKaehler318.reciprocal_differential,
    IntrinsicChartSections318.section_smul]
  rfl
end FourRootIntrinsicCanonicalFrames318
