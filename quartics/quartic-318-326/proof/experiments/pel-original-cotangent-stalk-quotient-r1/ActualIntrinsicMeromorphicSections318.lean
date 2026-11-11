module
public import ActualLocalizationDifferentialFrame318
public import IntrinsicAffineSectionEquiv318
public section
noncomputable section
namespace ActualIntrinsicMeromorphicSections318
open AlgebraicGeometry CategoryTheory
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
variable (R:Type*) [CommRing R] [IsDomain R] [Algebra ℂ R] (d:R)(hd:d≠0)
abbrev S:=ActualLocalizationDifferentialFrame318.Chart R d
abbrev K:=FractionRing R
@[expose] def scalarMap:S R d→ₐ[ℂ]K R where
  __:=ActualLocalizationDifferentialFrame318.embedding R d hd
  commutes' c:=by
    rw [IsScalarTower.algebraMap_apply ℂ R (S R d),
      ActualLocalizationDifferentialFrame318.on_source]
    exact (IsScalarTower.algebraMap_apply ℂ R (K R) c).symm
variable {Y:Scheme} (j:Spec (CommRingCat.of (S R d))⟶Y) [IsOpenImmersion j]
  (p:Y⟶Spec (CommRingCat.of ℂ))
  (h:j≫p=Spec.map (CommRingCat.ofHom (algebraMap ℂ (S R d))))
/-- Meromorphic realization of ACTUAL intrinsic sheaf sections: first
use the genuine universal differential chart comparison, then extend
its algebraic differential into the unchanged original fraction field. -/
@[expose] def realization:
    Γ(FamilyIntrinsicDifferentials318.omega p,j ''ᵁ ⊤)→+
      KaehlerDifferential ℂ (K R):=
  (AlgHomDifferential318.map (scalarMap R d hd)).toAddMonoidHom.comp
    (IntrinsicAffineSectionEquiv318.equivalence j p h).symm.toAddMonoidHom
lemma realization_section(ω:KaehlerDifferential ℂ (S R d)):
    realization R d hd j p h (IntrinsicChartSections318.sectionMap j p h ω)=
      AlgHomDifferential318.map (scalarMap R d hd) ω:=by
  change AlgHomDifferential318.map (scalarMap R d hd)
    ((IntrinsicAffineSectionEquiv318.equivalence j p h).symm
      ((IntrinsicAffineSectionEquiv318.equivalence j p h) ω))=_
  rw [AddEquiv.symm_apply_apply]
/-- Exact actual universal derivative square; this ties the meromorphic
one-form to the intrinsic sheaf instead of renaming a coefficient type. -/
theorem realization_derivative(s:S R d):
    realization R d hd j p h
      ((FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of (S R d))).inv s)))=
      KaehlerDifferential.D ℂ (K R) (scalarMap R d hd s):=by
  rw [←IntrinsicChartSections318.section_D,realization_section,AlgHomDifferential318.map_D]
end ActualIntrinsicMeromorphicSections318
