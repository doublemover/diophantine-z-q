module
public import FourRootProjectiveProjection318
public import FourRootIntrinsicCanonicalFrames318
public import IntrinsicDifferentialSectionPullback318
public import Mathlib.RingTheory.Kaehler.Polynomial
public section
noncomputable section
namespace FourRootProjectiveDifferential318
open AlgebraicGeometry CategoryTheory Opposite Polynomial
open FourRootGluedScheme318 FourRootProjectiveProjection318
variable (b:Fin 4→ℂ)
abbrev Base:=ProjectiveJLine318.scheme ℂ
abbrev baseStructure:=ProjectiveJLine318.structureMap ℂ
@[expose] def baseOmega:Base.Modules:=FamilyIntrinsicDifferentials318.omega baseStructure
/-- The genuine derivative of the ORIGINAL whole degree16 Scheme map,
in pushforward form; it is derived from the universal derivation. -/
@[expose] def map:baseOmega⟶(Scheme.Modules.pushforward (projection b)).obj
    (FourRootIntrinsicCanonicalFrames318.omega b):=
  IntrinsicDifferentialPullback318.map (projection b) (structureMap b) baseStructure (over_base b)
/-- Its actual pullback adjoint, not a selected generic-field map or a
record of local desired coefficients. -/
@[expose] def derivative:(Scheme.Modules.pullback (projection b)).obj baseOmega⟶
    FourRootIntrinsicCanonicalFrames318.omega b:=
  IntrinsicDifferentialPullback318.pullbackMap (projection b) (structureMap b) baseStructure (over_base b)
lemma derivative_adjoint:
    (Scheme.Modules.pullbackPushforwardAdjunction (projection b)).homEquiv _ _ (derivative b)=map b:=
  IntrinsicDifferentialPullback318.pullbackMap_adjoint _ _ _ _
lemma original_D(U:Base.Opens)(s:Γ(Base,U)):
    (map b).val.app (op U) ((FamilyIntrinsicDifferentials318.D baseStructure).d s)=
      (FamilyIntrinsicDifferentials318.D (structureMap b)).d ((projection b).app U s):=
  IntrinsicDifferentialPullback318.map_D _ _ _ _ U s

@[expose] def finiteBaseChart:Spec (CommRingCat.of (Polynomial ℂ))⟶Base:=JLineAtlas318.chart ℂ 1
/-- Actual original infinity chart: v=1/(t-b0), hence its pullback is
u². This is a chart of the SAME original projective target after its
specified affine translation, not a different base morphism. -/
@[expose] def infinityBaseChart:Spec (CommRingCat.of (Polynomial ℂ))⟶Base:=
  JLineAtlas318.chart ℂ 0≫ProjectiveAffineLine318.map ℂ 1 (b 0)
instance finiteBaseChart_open:IsOpenImmersion finiteBaseChart:=by unfold finiteBaseChart;infer_instance
instance infinityBaseChart_open:IsOpenImmersion (infinityBaseChart b):=by
  change IsOpenImmersion (JLineAtlas318.chart ℂ 0≫(ProjectiveAffineLine318.iso ℂ 1 (b 0)).hom)
  infer_instance
lemma finite_base_structure:finiteBaseChart≫baseStructure=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))):=
  JLineAtlas318.chart_over_base ℂ 1
lemma infinity_base_structure:infinityBaseChart b≫baseStructure=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))):=by
  rw [infinityBaseChart,Category.assoc,ProjectiveAffineCharts318.map_over_base]
  exact JLineAtlas318.chart_over_base ℂ 0
@[expose] def finiteBaseFrame:
    (Scheme.Modules.restrictFunctor finiteBaseChart).obj (SheafOfModules.unit Base.ringCatSheaf)≅
      baseOmega.restrict finiteBaseChart:=
  IntrinsicChartFrames318.frame finiteBaseChart baseStructure finite_base_structure
    (KaehlerDifferential.polynomialEquiv ℂ)
@[expose] def infinityBaseFrame:
    (Scheme.Modules.restrictFunctor (infinityBaseChart b)).obj (SheafOfModules.unit Base.ringCatSheaf)≅
      baseOmega.restrict (infinityBaseChart b):=
  IntrinsicChartFrames318.frame (infinityBaseChart b) baseStructure (infinity_base_structure b)
    (KaehlerDifferential.polynomialEquiv ℂ)
@[expose] def finiteBaseGenerator:Γ(baseOmega,finiteBaseChart ''ᵁ ⊤):=
  IntrinsicChartSections318.sectionMap finiteBaseChart baseStructure finite_base_structure
    (KaehlerDifferential.D ℂ (Polynomial ℂ) X)
@[expose] def infinityBaseGenerator:Γ(baseOmega,infinityBaseChart b ''ᵁ ⊤):=
  IntrinsicChartSections318.sectionMap (infinityBaseChart b) baseStructure (infinity_base_structure b)
    (KaehlerDifferential.D ℂ (Polynomial ℂ) X)
lemma finiteBaseFrame_one:(finiteBaseFrame.hom.val.app (op ⊤)) 1=finiteBaseGenerator:=by
  apply IntrinsicChartFrames318.frame_one
  rw [KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X]
lemma infinityBaseFrame_one:(infinityBaseFrame b).hom.val.app (op ⊤) 1=infinityBaseGenerator b:=by
  apply IntrinsicChartFrames318.frame_one
  rw [KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X]
end FourRootProjectiveDifferential318
