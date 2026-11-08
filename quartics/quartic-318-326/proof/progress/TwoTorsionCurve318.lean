module
public import ShortTwoTorsion318
public import AffineEquationFunctor318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace TwoTorsionCurve318
open CategoryTheory AlgebraicGeometry Polynomial
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type} [CommRing R] (A B:R)

lemma root_relation :
    (AdjoinRoot.root (ShortTwoTorsion318.polynomial A B))^3+
      algebraMap R (ShortTwoTorsion318.Ring A B) A*AdjoinRoot.root (ShortTwoTorsion318.polynomial A B)+
      algebraMap R (ShortTwoTorsion318.Ring A B) B=0 := by
  have h:=AdjoinRoot.mk_self (f:=ShortTwoTorsion318.polynomial A B)
  change AdjoinRoot.mk (ShortTwoTorsion318.polynomial A B) (X^3+C A*X+C B)=0 at h
  rw [map_add,map_add,map_pow,map_mul,AdjoinRoot.mk_X,AdjoinRoot.mk_C,AdjoinRoot.mk_C] at h
  exact h

@[expose] def coordinateMap :
    ShortAffineJacobian318.Ring A B→ₐ[R]ShortTwoTorsion318.Ring A B :=
  AffineEquationFunctor318.toHom A B
    ⟨(AdjoinRoot.root (ShortTwoTorsion318.polynomial A B),0),by
      change (0:ShortTwoTorsion318.Ring A B)^2-
        (AdjoinRoot.root (ShortTwoTorsion318.polynomial A B))^3-
        algebraMap R (ShortTwoTorsion318.Ring A B) A*AdjoinRoot.root (ShortTwoTorsion318.polynomial A B)-
        algebraMap R (ShortTwoTorsion318.Ring A B) B=0
      linear_combination -root_relation A B⟩

lemma coordinateMap_x : coordinateMap A B (ShortAffineJacobian318.x A B)=
    AdjoinRoot.root (ShortTwoTorsion318.polynomial A B) :=
  AffineEquationFunctor318.toHom_x _ _ _
lemma coordinateMap_y : coordinateMap A B (ShortAffineJacobian318.y A B)=0 :=
  AffineEquationFunctor318.toHom_y _ _ _

lemma coordinateMap_surjective : Function.Surjective (coordinateMap A B) := by
  intro z
  obtain ⟨f,rfl⟩:=AdjoinRoot.mk_surjective z
  refine ⟨aeval (ShortAffineJacobian318.x A B) f,?_⟩
  rw [←Polynomial.aeval_algHom_apply,coordinateMap_x,AdjoinRoot.aeval_eq]

@[expose] def scheme : Scheme:=Spec (CommRingCat.of (ShortTwoTorsion318.Ring A B))
@[expose] def structureMap : scheme A B⟶Spec (CommRingCat.of R):=
  Spec.map (CommRingCat.ofHom (algebraMap R (ShortTwoTorsion318.Ring A B)))
@[expose] def inclusion : scheme A B⟶ShortAffineScheme318.scheme A B:=
  Spec.map (CommRingCat.ofHom (coordinateMap A B).toRingHom)

theorem inclusion_closed : IsClosedImmersion (inclusion A B):=
  IsClosedImmersion.spec_of_surjective _ (coordinateMap_surjective A B)

theorem inclusion_over_base : inclusion A B≫ShortAffineScheme318.structureMap A B=
    structureMap A B:=by
  unfold inclusion ShortAffineScheme318.structureMap structureMap scheme ShortAffineScheme318.scheme
  rw [←Spec.map_comp]
  exact congrArg (fun f=>Spec.map (CommRingCat.ofHom f)) (coordinateMap A B).comp_algebraMap

theorem finite_etale (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsFinite (structureMap A B) ∧ Etale (structureMap A B):=by
  letI:=ShortTwoTorsion318.finite A B
  letI:=ShortTwoTorsion318.etale A B hD
  constructor
  · exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  · exact (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)


theorem flat_surjective [Nontrivial R] :
    Flat (structureMap A B) ∧ Surjective (structureMap A B) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr (ShortTwoTorsion318.faithfullyFlat A B)

variable {S:Type} [CommRing S] [Algebra R S]

/-- The closed subscheme represents y=0 over every coefficient algebra,
including rings with nilpotents, not only field-valued points. -/
theorem factor_zero_y (φ:ShortAffineJacobian318.Ring A B→ₐ[R]S)
    (hy:φ (ShortAffineJacobian318.y A B)=0) :
    ∃! ψ:ShortTwoTorsion318.Ring A B→ₐ[R]S, ψ.comp (coordinateMap A B)=φ := by
  let x:=φ (ShortAffineJacobian318.x A B)
  have hrel:=congrArg φ (ShortAffineJacobian318.relation A B)
  simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,hy] at hrel
  have hx:(ShortTwoTorsion318.polynomial A B).eval₂ (algebraMap R S) x=0 := by
    simp only [ShortTwoTorsion318.polynomial,eval₂_add,eval₂_pow,eval₂_X,eval₂_mul,eval₂_C]
    change x^3+algebraMap R S A*x+algebraMap R S B=0
    linear_combination -hrel
  let ψ:=AdjoinRoot.liftAlgHom (ShortTwoTorsion318.polynomial A B) (Algebra.ofId R S) x hx
  refine ⟨ψ,?_,?_⟩
  · apply AffineEquationFunctor318.hom_ext
    · simp only [AlgHom.comp_apply,coordinateMap_x,ψ,AdjoinRoot.liftAlgHom_root]
      rfl
    · simp only [AlgHom.comp_apply,coordinateMap_y,map_zero,hy]
  · intro χ hχ
    apply AdjoinRoot.algHom_ext
    have hh:=AlgHom.congr_fun hχ (ShortAffineJacobian318.x A B)
    simpa only [AlgHom.comp_apply,coordinateMap_x,ψ,AdjoinRoot.liftAlgHom_root] using hh

end TwoTorsionCurve318
