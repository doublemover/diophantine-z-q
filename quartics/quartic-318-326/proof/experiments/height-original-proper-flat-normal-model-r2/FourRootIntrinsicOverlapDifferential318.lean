module
public import FourRootOverlapOriginalDifferential318
public import FourRootCanonicalFiniteSectionPropagation318
public section
noncomputable section
namespace FourRootIntrinsicOverlapDifferential318
open AlgebraicGeometry CategoryTheory
open FourRootCoordinateOverlap318 FourRootGluedScheme318 FourRootIntrinsicCanonicalFrames318
open FourRootCanonicalFiniteSectionPropagation318
variable (b:Fin 4→ℂ)
@[expose] def embedding:overlapScheme b⟶scheme b:=intoInfinity b≫infinityChart b
instance embedding_open:IsOpenImmersion (embedding b):=by unfold embedding;infer_instance
lemma structure:embedding b≫structureMap b=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (InfinityOverlap b))):=by
  rw [embedding,Category.assoc,infinity_structure]
  unfold intoInfinity infinityBase
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (IsScalarTower.algebraMap_apply ℂ (Infinity b) (InfinityOverlap b) c).symm
@[expose] def domain:(scheme b).Opens:=embedding b ''ᵁ ⊤
lemma finite_route:Spec.map (CommRingCat.ofHom (toInfinityBase b).toRingHom)≫finiteChart b=embedding b:=by
  rw [←intoFinite_eq,chart_overlap]
  rfl
instance finite_map_open:IsOpenImmersion (Spec.map (CommRingCat.ofHom (toInfinityBase b).toRingHom)):=by
  rw [←intoFinite_eq]
  infer_instance
lemma domain_le_finite:domain b≤finiteOpen b:=by
  rw [domain,←finite_route]
  exact OpenChartSections318.imageLE _ _
lemma domain_le_infinity:domain b≤infinityChart b ''ᵁ ⊤:=
  OpenChartSections318.imageLE (intoInfinity b) (infinityChart b)
lemma whole_infinity_structure:infinityChart b≫structureMap b=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Infinity b))):=infinity_structure b
@[expose] def wholeDu:Γ(omega b,infinityChart b ''ᵁ ⊤):=
  IntrinsicChartSections318.sectionMap (infinityChart b) (structureMap b) (whole_infinity_structure b)
    (KaehlerDifferential.D ℂ (Infinity b) (FourRootInfinityCoordinateRing318.coordinate b none))
@[expose] def scalar:InfinityOverlap b→+*Γ(scheme b,domain b):=
  ((embedding b).appIso ⊤).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (InfinityOverlap b))).inv.hom
lemma dt_restriction:
    (omega b).presheaf.map (homOfLE (domain_le_finite b)).op (wholeDt b)=
    IntrinsicChartSections318.sectionMap (embedding b) (structureMap b) (structure b)
      (KaehlerDifferential.D ℂ (InfinityOverlap b)
        (toInfinityBase b (FourRootAffineCoordinateRing318.coordinate b none))):=by
  have h:=IntrinsicChartNaturality318.section_restrict_to (toInfinityBase b) (finiteChart b)
    (structureMap b) (whole_finite_structure b)
    (embedding b) (structure b) (finite_route b) (domain_le_finite b)
    (KaehlerDifferential.D ℂ (Affine b) (FourRootAffineCoordinateRing318.coordinate b none))
  rw [AlgHomDifferential318.map_D] at h
  exact h
lemma du_restriction:
    (omega b).presheaf.map (homOfLE (domain_le_infinity b)).op (wholeDu b)=
    IntrinsicChartSections318.sectionMap (embedding b) (structureMap b) (structure b)
      (KaehlerDifferential.D ℂ (InfinityOverlap b) (u b)):=by
  have h:=IntrinsicChartNaturality318.section_restrict
    (IsScalarTower.toAlgHom ℂ (Infinity b) (InfinityOverlap b)) (infinityChart b)
    (structureMap b) (whole_infinity_structure b) (structure b)
    (KaehlerDifferential.D ℂ (Infinity b) (FourRootInfinityCoordinateRing318.coordinate b none))
  rw [AlgHomDifferential318.map_D] at h
  exact h
/-- True meromorphic transition for the SAME intrinsic Omega sections
on the ACTUAL full finite/infinity overlap. The inverse u is a regular
function here; no fraction-field frame equality is assumed. -/
theorem original_dt_transition:
    (omega b).presheaf.map (homOfLE (domain_le_finite b)).op (wholeDt b)=
      scalar b (-(2:InfinityOverlap b)*(ui b)^3) •
        (omega b).presheaf.map (homOfLE (domain_le_infinity b)).op (wholeDu b):=by
  rw [dt_restriction,FourRootOverlapOriginalDifferential318.original_dt,
    IntrinsicChartSections318.section_smul,du_restriction]
  rfl
/-- Genuine pole-cleared equality on the actual overlap of sheaf
sections, with original u and original dt. -/
theorem cleared_original_dt:
    scalar b ((u b)^3) • (omega b).presheaf.map (homOfLE (domain_le_finite b)).op (wholeDt b)=
      scalar b (-(2:InfinityOverlap b)) •
        (omega b).presheaf.map (homOfLE (domain_le_infinity b)).op (wholeDu b):=by
  rw [dt_restriction,du_restriction]
  change scalar b ((u b)^3) • IntrinsicChartSections318.sectionMap (embedding b) (structureMap b)
    (structure b) _=scalar b (-(2:InfinityOverlap b)) •
      IntrinsicChartSections318.sectionMap (embedding b) (structureMap b) (structure b) _
  rw [←IntrinsicChartSections318.section_smul,←IntrinsicChartSections318.section_smul]
  exact congrArg (IntrinsicChartSections318.sectionMap (embedding b) (structureMap b) (structure b))
    (FourRootOverlapOriginalDifferential318.cleared_original_dt b)
end FourRootIntrinsicOverlapDifferential318
