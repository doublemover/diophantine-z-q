module
public import ActualRationalSectionPropagation318
public import FourRootCanonicalRationalEquations318
public import IntrinsicChartNaturality318
public section
noncomputable section
namespace FourRootCanonicalFiniteSectionPropagation318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootCanonicalRationalEquations318 FourRootActualCanonicalLine318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
abbrev A:=FourRootAffineCoordinateRing318.Ring b
local instance integral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
@[expose] def finiteOpen:(scheme b).Opens:=finiteChart b ''ᵁ ⊤
lemma whole_finite_structure:finiteChart b≫structureMap b=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (A b))):=
  FourRootGluedScheme318.finite_structure b
/-- Original dt is genuinely regular on the ENTIRE finite chart, not
only on the chosen reference root-zero principal neighborhood. -/
@[expose] def wholeDt:Γ(omega b,finiteOpen b):=
  IntrinsicChartSections318.sectionMap (finiteChart b) (structureMap b) (whole_finite_structure b)
    (KaehlerDifferential.D ℂ (A b) (FourRootAffineCoordinateRing318.coordinate b none))
@[expose] def chartMap(i:Fin 4):A b→ₐ[ℂ]FiniteRing b i:=IsScalarTower.toAlgHom ℂ (A b) (FiniteRing b i)
lemma chart_le(i:Fin 4):finiteEmbedding b i ''ᵁ ⊤≤finiteOpen b:=
  OpenChartSections318.imageLE (Spec.map (CommRingCat.ofHom (algebraMap (A b) (FiniteRing b i))))
    (finiteChart b)
lemma ambient_le(i:Fin 4):opens b hb (some i)≤finiteOpen b:=by
  rw [←(finiteEmbedding b i).image_top_eq_opensRange]
  exact chart_le b i
lemma wholeDt_on_chart(i:Fin 4):
    (omega b).presheaf.map (homOfLE (chart_le b i)).op (wholeDt b)=
      (FamilyIntrinsicDifferentials318.D (structureMap b)).d
        (((finiteEmbedding b i).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of (FiniteRing b i))).inv
            (FourRootActualBranchKaehler318.sourceParameter b i))):=by
  have he:=IntrinsicChartNaturality318.section_restrict (chartMap b i) (finiteChart b)
    (structureMap b) (whole_finite_structure b) (finite_structure b i)
    (KaehlerDifferential.D ℂ (A b) (FourRootAffineCoordinateRing318.coordinate b none))
  rw [AlgHomDifferential318.map_D,IntrinsicChartSections318.section_D] at he
  exact he
lemma wholeDt_reference:
    (omega b).presheaf.map (homOfLE (ambient_le b hb 0)).op (wholeDt b)=referenceSection b hb:=by
  rw [←ActualRationalSectionPropagation318.restrict_chain (omega b)
    (show opens b hb (some 0)≤finiteEmbedding b 0 ''ᵁ ⊤ from (reference_open b hb).symm.le)
    (chart_le b 0) (wholeDt b),wholeDt_on_chart]
  rfl
/-- Every actual local rational equation is the genuine coefficient of
the SAME original whole-finite-chart dt section wherever that section
is regular. The reference overlap is no longer a domain restriction. -/
theorem equation_on_finite(i:Option (Fin 4))(W:(scheme b).Opens)[Nonempty W]
    (hi:W≤opens b hb i)(hfin:W≤finiteOpen b):
    (scheme b).germToFunctionField W
      ((OpenLineFrameCoordinates318.frame (omega b) (opens b hb i) (frame b hb i) W hi).symm
        ((omega b).presheaf.map (homOfLE hfin).op (wholeDt b)))=localEquation b hb i:=by
  apply ActualRationalSectionPropagation318.from_larger_open (omega b) (opens b hb) (frame b hb)
    (some 0) (referenceCoefficient b hb) (finiteOpen b) (ambient_le b hb 0) (wholeDt b)
    ?_ i W hi hfin
  rw [wholeDt_reference]
  rfl
end FourRootCanonicalFiniteSectionPropagation318
