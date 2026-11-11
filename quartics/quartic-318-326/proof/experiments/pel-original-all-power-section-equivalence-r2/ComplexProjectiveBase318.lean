module
public import ComplexProjectiveSchemePoint318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public section
noncomputable section
namespace ComplexProjectiveBase318
open AlgebraicGeometry CategoryTheory ComplexProjectiveMarkerPoint318
variable {ι:Type*}
local instance standardGrading:GradedAlgebra (grading (ι:=ι)):=MvPolynomial.gradedAlgebra
abbrev DegreeZero:=grading (ι:=ι) 0

/-- The literal degree-zero part is exactly C, with its actual inclusion
into the same polynomial ring. No alternate graded ring is substituted. -/
@[expose] def constants:ℂ≃+*DegreeZero (ι:=ι) where
  toFun c:=⟨MvPolynomial.C c,MvPolynomial.isHomogeneous_C ι c⟩
  invFun p:=p.val.coeff 0
  left_inv c:=by simp
  right_inv p:=by
    apply Subtype.ext
    exact (MvPolynomial.homogeneousComponent_zero p.val).symm.trans
      (MvPolynomial.homogeneousComponent_eq_self p.property)
  map_mul' c d:=by apply Subtype.ext;exact map_mul MvPolynomial.C c d
  map_add' c d:=by apply Subtype.ext;exact map_add MvPolynomial.C c d
lemma constants_inclusion(c:ℂ):
    algebraMap (DegreeZero (ι:=ι)) (Equations (ι:=ι)) (constants c)=MvPolynomial.C c:=rfl
lemma constants_inclusion_hom:
    (algebraMap (DegreeZero (ι:=ι)) (Equations (ι:=ι))).comp constants.toRingHom=
      algebraMap ℂ (Equations (ι:=ι)):=by
  ext c
  exact constants_inclusion c

@[expose] def baseIso:Spec (CommRingCat.of (DegreeZero (ι:=ι)))≅
    ComplexProjectiveSchemePoint318.ComplexPoint:=
  Scheme.Spec.mapIso (constants (ι:=ι)).toCommRingCatIso.op
@[expose] def structureMap:AlgebraicGeometry.Proj (grading (ι:=ι))⟶
    ComplexProjectiveSchemePoint318.ComplexPoint:=
  Proj.toSpecZero grading≫baseIso.hom

/-- Finite type over the ACTUAL zero ring follows from finite type of the
original polynomial C-algebra and the literal constant inclusion square. -/
lemma finite_type_zero [Finite ι]:Algebra.FiniteType (DegreeZero (ι:=ι)) (Equations (ι:=ι)):=by
  have h:(algebraMap ℂ (Equations (ι:=ι))).FiniteType:=
    RingHom.finiteType_algebraMap.mpr inferInstance
  rw [←constants_inclusion_hom] at h
  exact RingHom.finiteType_algebraMap.mp (RingHom.FiniteType.of_comp_finiteType h)
instance proper_structure [Finite ι]:IsProper (structureMap (ι:=ι)):=by
  haveI:=finite_type_zero (ι:=ι)
  dsimp [structureMap]
  infer_instance

lemma point_over(v:ι→ℂ)(hv:∃j,v j≠0):
    ComplexProjectiveSchemePoint318.point v hv≫structureMap=𝟙 _:=by
  rw [structureMap,←Category.assoc]
  rw [ComplexProjectiveSchemePoint318.point,Proj.fromOfGlobalSections_toSpecZero]
  have hc:((ComplexProjectiveSchemePoint318.evaluation v).comp
      (algebraMap (DegreeZero (ι:=ι)) (Equations (ι:=ι)))).comp constants.toRingHom=
      ComplexProjectiveSchemePoint318.scalar:=by
    ext c
    change ComplexProjectiveSchemePoint318.scalar (MvPolynomial.eval v (MvPolynomial.C c))=
      ComplexProjectiveSchemePoint318.scalar c
    rw [MvPolynomial.eval_C]
  change (ComplexProjectiveSchemePoint318.ComplexPoint.toSpecΓ≫
    Spec.map (CommRingCat.ofHom ((ComplexProjectiveSchemePoint318.evaluation v).comp
      (algebraMap (DegreeZero (ι:=ι)) (Equations (ι:=ι))))))≫
    Spec.map (CommRingCat.ofHom constants.toRingHom)=𝟙 _
  rw [Category.assoc,←Spec.map_comp,←CommRingCat.ofHom_comp,hc]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (CommRingCat.of ℂ)
end ComplexProjectiveBase318

