module
public import FourRootIntrinsicOverlapDifferential318
public import FourRootActualIntrinsicFrameComparison318
public import ActualOpenAffineCoefficientGerm318
public section
noncomputable section
namespace FourRootCanonicalInfinitySection318
open AlgebraicGeometry CategoryTheory
open FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootIntrinsicOverlapDifferential318 FourRootCanonicalRationalEquations318
open FourRootActualCanonicalLine318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
local instance integral:IsIntegral (scheme b):=FourRootWholeSchemeGeometry318.integral b hb
local instance overlapDomain:IsDomain (FourRootCoordinateOverlap318.InfinityOverlap b):=
  FourRootInfinityDomain318.infinity_overlap_domain b hb
local instance overlapNonempty:Nonempty (domain b):=by
  obtain ⟨p⟩:Nonempty (overlapScheme b):=inferInstance
  exact ⟨⟨embedding b p,⟨p,trivial,rfl⟩⟩⟩
abbrev U: (scheme b).Opens:=opens b hb none
@[expose] def W:(scheme b).Opens:=U b hb⊓domain b
local instance commonNonempty:Nonempty (W b hb):=
  FunctionFieldGluing318.intersection_nonempty (scheme b) (U b hb) (domain b)
lemma canonical_le:U b hb≤infinityEmbedding b hb ''ᵁ ⊤:=
  (infinityEmbedding b hb).image_top_eq_opensRange.symm.le
lemma chart_le:infinityEmbedding b hb ''ᵁ ⊤≤infinityChart b ''ᵁ ⊤:=
  OpenChartSections318.imageLE (Spec.map (CommRingCat.ofHom
    (algebraMap (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb)))) (infinityChart b)
lemma wholeDu_on_chart:
    (omega b).presheaf.map (homOfLE (chart_le b hb)).op (wholeDu b)=infinityGenerator b hb:=by
  have h:=IntrinsicChartNaturality318.section_restrict
    (IsScalarTower.toAlgHom ℂ (FourRootInfinityCoordinateRing318.Ring b) (InfinityRing b hb))
    (infinityChart b) (structureMap b) (whole_infinity_structure b)
    (FourRootIntrinsicCanonicalFrames318.infinity_structure b hb)
    (KaehlerDifferential.D ℂ (FourRootInfinityCoordinateRing318.Ring b)
      (FourRootInfinityCoordinateRing318.coordinate b none))
  rw [AlgHomDifferential318.map_D] at h
  exact h
@[expose] def e:
    Γ(scheme b,U b hb)≃ₗ[Γ(scheme b,U b hb)]Γ(omega b,U b hb):=
  OpenLineFrameCoordinates318.frame (omega b) (U b hb) (frame b hb none) (U b hb) le_rfl
/-- The actual du coefficient in the produced canonical frame, on the
ENTIRE original infinity canonical neighborhood, is a regular unit. -/
@[expose] def unitCoefficient:Γ(scheme b,U b hb):=
  (e b hb).symm ((omega b).presheaf.map
    (homOfLE ((canonical_le b hb).trans (chart_le b hb))).op (wholeDu b))
lemma unitCoefficient_unit:IsUnit (unitCoefficient b hb):=by
  unfold unitCoefficient
  rw [←ActualRationalSectionPropagation318.restrict_chain (omega b)
    (canonical_le b hb) (chart_le b hb),wholeDu_on_chart]
  exact FourRootActualIntrinsicFrameComparison318.infinity_generator_unit b hb
    (U b hb) (e b hb) (canonical_le b hb)
@[expose] def inverseU:(scheme b).functionField:=
  (scheme b).germToFunctionField (domain b) (scalar b (FourRootCoordinateOverlap318.ui b))
/-- The local rational equation for SAME original dt is now identified
with its genuine intrinsic du-frame coefficient, including the original
third-order pole. Equality is proved on the actual finite/infinity overlap
and propagated by true generic germs, not by an assumed frame transport. -/
theorem infinity_equation:
    localEquation b hb none=-(2:(scheme b).functionField)*(inverseU b hb)^3*
      (scheme b).germToFunctionField (U b hb) (unitCoefficient b hb):=by
  let hWU:W b hb≤U b hb:=inf_le_left
  let hWO:W b hb≤domain b:=inf_le_right
  let hWF:W b hb≤FourRootCanonicalFiniteSectionPropagation318.finiteOpen b:=
    hWO.trans (domain_le_finite b)
  let hWI:W b hb≤infinityChart b ''ᵁ ⊤:=hWO.trans (domain_le_infinity b)
  let eW:=OpenLineFrameCoordinates318.frame (omega b) (U b hb) (frame b hb none) (W b hb) hWU
  have hd:(omega b).presheaf.map (homOfLE hWF).op
      (FourRootCanonicalFiniteSectionPropagation318.wholeDt b)=
      (scheme b).presheaf.map (homOfLE hWO).op
        (scalar b (-(2:FourRootCoordinateOverlap318.InfinityOverlap b)*
          (FourRootCoordinateOverlap318.ui b)^3)) •
        (omega b).presheaf.map (homOfLE hWI).op (wholeDu b):=by
    rw [←ActualRationalSectionPropagation318.restrict_chain (omega b) hWO (domain_le_finite b),
      original_dt_transition,(omega b).val.map_smul,
      ActualRationalSectionPropagation318.restrict_chain]
  have hg:eW.symm ((omega b).presheaf.map (homOfLE hWI).op (wholeDu b))=
      (scheme b).presheaf.map (homOfLE hWU).op (unitCoefficient b hb):=by
    rw [←ActualRationalSectionPropagation318.restrict_chain (omega b) hWU
      ((canonical_le b hb).trans (chart_le b hb))]
    exact (OpenLineFrameCoordinates318.inverse_natural (omega b) (U b hb)
      (frame b hb none) le_rfl hWU _).symm
  have he:=FourRootCanonicalFiniteSectionPropagation318.equation_on_finite b hb none
    (W b hb) hWU hWF
  change (scheme b).germToFunctionField (W b hb) (eW.symm _)=_ at he
  rw [hd,map_smul,smul_eq_mul,hg,map_mul,
    AffineDominantNormRestriction318.germ_restrict,
    AffineDominantNormRestriction318.germ_restrict] at he
  have hs:(scheme b).germToFunctionField (domain b)
      (scalar b (-(2:FourRootCoordinateOverlap318.InfinityOverlap b)*
        (FourRootCoordinateOverlap318.ui b)^3))=
      -(2:(scheme b).functionField)*(inverseU b hb)^3:=by
    simp only [map_mul,map_neg,map_ofNat,map_pow,inverseU]
  rw [hs] at he
  exact he.symm
end FourRootCanonicalInfinitySection318
