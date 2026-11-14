module
public import FourRootCompletedSchemePoints318
public import FourRootSchemeSignAction318
public import PELOriginalContactSchemePoints318
public import PELOriginalCompletedContactDeck318
public section
noncomputable section
namespace FourRootSchemePointEquivariance318
open AlgebraicGeometry CategoryTheory
open FourRootNormalizedPointCharts318 FourRootCompletedSchemePoints318
open FourRootSchemeChartInputs318 FourRootCoordinateRingSigns318
variable (b:Fin 4→ℂ) (g:FourBinaryCharacters318.Group)
@[expose] def pointAction (q:SchemePoints b):SchemePoints b:=
  ⟨q.val≫FourRootSchemeSignAction318.action b g,by
    rw [Category.assoc,FourRootSchemeSignAction318.over_base]
    exact q.property⟩
lemma finite_input (f:FourRootAffineCoordinateRing318.Ring b→ₐ[ℂ]ℂ):
    finiteInput b f≫FourRootSchemeSignAction318.action b g=
      finiteInput b (f.comp (finiteEnd b g)):=by
  unfold finiteInput
  rw [Category.assoc,FourRootSchemeSignAction318.finite_action,←Category.assoc]
  unfold FourRootSchemeSignAction318.finiteMap
  rw [←Spec.map_comp]
  rfl
lemma infinity_input (f:FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]ℂ):
    infinityInput b f≫FourRootSchemeSignAction318.action b g=
      infinityInput b (f.comp (infinityEnd b g)):=by
  unfold infinityInput
  rw [Category.assoc,FourRootSchemeSignAction318.infinity_action,←Category.assoc]
  unfold FourRootSchemeSignAction318.infinityMap
  rw [←Spec.map_comp]
  rfl

lemma finite_equivariant (p:FinitePoints b):
    pointAction b g (finitePoint b p)=
      finitePoint b (FourRootNormalizedSignAction318.finite b g p):=by
  let f:FourRootAffineCoordinateRing318.Ring b→ₐ[ℂ]ℂ:=
    (FourRootAffineCoordinateRing318.pointEquiv b).symm p
  have he:f.comp (finiteEnd b g)=
      (FourRootAffineCoordinateRing318.pointEquiv b).symm
        (FourRootNormalizedSignAction318.finite b g p):=by
    apply (FourRootAffineCoordinateRing318.pointEquiv b).injective
    rw [Equiv.apply_symm_apply]
    have hf:(FourRootAffineCoordinateRing318.point b f)=p:=
      (FourRootAffineCoordinateRing318.pointEquiv b).apply_symm_apply p
    exact (finite_point b g f).trans (congrArg (FourRootNormalizedSignAction318.finite b g) hf)
  apply Subtype.ext
  change finiteInput b f≫FourRootSchemeSignAction318.action b g=_
  rw [finite_input,he]
  rfl
lemma infinity_equivariant (p:InfinityPoints b):
    pointAction b g (infinityPoint b p)=
      infinityPoint b (FourRootNormalizedSignAction318.infinity b g p):=by
  let f:FourRootInfinityCoordinateRing318.Ring b→ₐ[ℂ]ℂ:=
    (FourRootInfinityCoordinateRing318.pointEquiv b).symm p
  have he:f.comp (infinityEnd b g)=
      (FourRootInfinityCoordinateRing318.pointEquiv b).symm
        (FourRootNormalizedSignAction318.infinity b g p):=by
    apply (FourRootInfinityCoordinateRing318.pointEquiv b).injective
    rw [Equiv.apply_symm_apply]
    have hf:(FourRootInfinityCoordinateRing318.point b f)=p:=
      (FourRootInfinityCoordinateRing318.pointEquiv b).apply_symm_apply p
    exact (infinity_point b g f).trans (congrArg (FourRootNormalizedSignAction318.infinity b g) hf)
  apply Subtype.ext
  change infinityInput b f≫FourRootSchemeSignAction318.action b g=_
  rw [infinity_input,he]
  rfl

/-- The algebraic Scheme automorphism acts on ALL complex points as the
same independently normalized finite/infinity root sign action. -/
theorem completed_equivariant (p:Completed b):
    pointAction b g (schemePointEquiv b p)=
      schemePointEquiv b (FourRootNormalizedSignAction318.action b g p):=by
  rcases p with p|s
  · exact finite_equivariant b g p
  · change pointAction b g (infinityPoint b (center b s))=_
    rw [infinity_equivariant]
    apply congrArg (infinityPoint b)
    apply Subtype.ext
    apply Prod.ext
    · change FourBinaryCharacters318.coordinate (F:=ℂ) 0 g*0=0
      exact mul_zero _
    · rfl

/-- The ORIGINAL inertia/deck action now agrees with an independently
constructed actual Scheme automorphism at every original point, including
all finite branch fibers and all eight normalized infinity points. -/
theorem original_equivariant (g:PELOriginalMaximalQuotient318.Labels)
    (p:PELUnlevelledComplexBase318.UnlevelledBase):
    PELOriginalContactSchemePoints318.comparison (g • p)=
      pointAction PELOriginalCommonContactBase318.branches (OriginalContactInertiaBasis318.basis g)
        (PELOriginalContactSchemePoints318.comparison p):=by
  change schemePointEquiv _ (PELOriginalCompletedContactPoints318.completedMap (g • p))=_
  rw [PELOriginalCompletedContactDeck318.equivariant]
  exact (completed_equivariant _ _ _).symm
end FourRootSchemePointEquivariance318
