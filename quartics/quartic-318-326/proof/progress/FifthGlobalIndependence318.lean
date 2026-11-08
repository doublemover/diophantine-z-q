module
public import FifthGlobalDifferential318
public import FiveInverseRootIndependence318
public import ContactCharacterGlobalIndependence318
public section
noncomputable section
namespace FifthGlobalIndependence318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open FifthFormLocalCoefficients318 ContactOverlapIntrinsic318
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
local instance rawField : Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero : CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
abbrev M:=ContactIntrinsicDifferentials318.omega units
@[expose] def form:KaehlerDifferential ℚ O:=
  ContactOverlapAlgebraMaps318.branchMap units 0 (branchCoefficient 0) •
    FifthFormCommonOpen318.form (chosen 0)

theorem restrict:M.presheaf.map (homOfLE (show embedding units ''ᵁ ⊤≤⊤ from le_top)).op
    FifthGlobalDifferential318.differential=
      IntrinsicChartSections318.sectionMap (embedding units)
        (ContactIntrinsicDifferentials318.structureMap units) (over_Q units) form:=
  (FifthGlobalDifferential318.common_restrict 0).trans
    (FifthFormCommonOpen318.weighted_eq_section (chosen 0) _)

theorem raw_formula:SourceOpenFractionField318.openEmbedding units
    (ContactUnbranchedDifferentialFrame318.frame units form)=FifthCharacterField318.root⁻¹:=by
  change SourceOpenFractionField318.openEmbedding units
    (ContactUnbranchedDifferentialFrame318.frame units
      (ContactOverlapAlgebraMaps318.branchMap units 0 (branchCoefficient 0) •
        FifthFormCommonOpen318.form (chosen 0)))=_
  rw [map_smul,smul_eq_mul,map_mul]
  change SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.branchMap units 0 (branchCoefficient 0))*
      ContactCharacterFrameValues318.rawValue
        (ContactCharacterAffinePullback318.finiteForm (chosen 0))=_
  rw [branch_coefficient_image,common_coefficient]

theorem constants_restrict (a:ℚ):
    (ContactGlobalSmooth318.Model units).presheaf.map (homOfLE (show
      embedding units ''ᵁ ⊤≤⊤ from le_top)).op
        (ContactCharacterGlobalIndependence318.constants a)=
          ScaledGlobalSectionRestriction318.scalar (embedding units) (algebraMap ℚ O a):=by
  exact DFunLike.congr_fun (RingHom.ext_rat
    (((ContactGlobalSmooth318.Model units).presheaf.map (homOfLE (show
      embedding units ''ᵁ ⊤≤⊤ from le_top)).op).hom.comp
        ContactCharacterGlobalIndependence318.constants)
    (((embedding units).appIso ⊤).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom |>.comp (algebraMap ℚ O))) a

/-- Five actual regular global intrinsic forms are rationally linearly
independent. This does not assert that they exhaust all global forms. -/
theorem independent (a:Fin 4→ℚ) (b:ℚ)
    (h:(∑i,ContactCharacterGlobalIndependence318.constants (a i) •
      ContactCharacterDifferentials318.differential i)+
        ContactCharacterGlobalIndependence318.constants b • FifthGlobalDifferential318.differential=0):
    (∀i,a i=0) ∧ b=0:=by
  have e:=congrArg (M.presheaf.map
    (homOfLE (show embedding units ''ᵁ ⊤≤⊤ from le_top)).op) h
  simp only [map_add,map_sum,Scheme.Modules.map_smul,map_zero,constants_restrict,
    FifthFormCommonOpen318.global_restrict,restrict] at e
  have hk:(∑i,algebraMap ℚ O (a i) • FifthFormCommonOpen318.form i)+
      algebraMap ℚ O b • form=0:=by
    apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective (embedding units)
      (ContactIntrinsicDifferentials318.structureMap units) (over_Q units)).1
    simp only [map_add,map_sum,map_zero,IntrinsicChartSections318.section_smul]
    exact e
  have hr:=congrArg (fun v:KaehlerDifferential ℚ O=>
    SourceOpenFractionField318.openEmbedding units
      (ContactUnbranchedDifferentialFrame318.frame units v)) hk
  simp only [map_add,map_sum,map_smul,smul_eq_mul,map_mul,map_zero,
    RingHom.map_rat_algebraMap] at hr
  change (∑i,algebraMap ℚ L (a i)*ContactCharacterFrameValues318.rawValue
      (ContactCharacterAffinePullback318.finiteForm i))+
      algebraMap ℚ L b*SourceOpenFractionField318.openEmbedding units
        (ContactUnbranchedDifferentialFrame318.frame units form)=0 at hr
  rw [raw_formula] at hr
  simp only [ContactCharacterFrameValues318.raw_formula,←mul_assoc,←map_mul] at hr
  have hh:=FiveInverseRootIndependence318.independent
    (fun i=>a i*((CharacterPublishedModels318.scaleUnit i:ℚ)/2)) b hr
  refine ⟨fun i=>?_,hh.2⟩
  exact (mul_eq_zero.mp (hh.1 i)).resolve_right
    (div_ne_zero (Units.ne_zero _) (by norm_num))
theorem nonzero:FifthGlobalDifferential318.differential≠0:=by
  intro hz
  have h:(∑i:Fin 4,ContactCharacterGlobalIndependence318.constants (0:ℚ) •
      ContactCharacterDifferentials318.differential i)+
        ContactCharacterGlobalIndependence318.constants 1 • FifthGlobalDifferential318.differential=0:=by
    simp only [map_zero,zero_smul,Finset.sum_const_zero,hz,smul_zero,add_zero]
  exact one_ne_zero (independent (fun _=>0) 1 h).2
end FifthGlobalIndependence318
