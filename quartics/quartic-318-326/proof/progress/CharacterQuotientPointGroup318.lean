module
public import CharacterQuotientOperations318
public import RationalSchemePointGroup318
public import Mathlib.Algebra.Group.TransferInstance
public section
noncomputable section
namespace CharacterQuotientPointGroup318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CharacterQuotientOperations318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (i:Fin 4) {T:Scheme} (b:T⟶Spec (CommRingCat.of ℚ))
abbrev Points:=CompletedIsoOperations318.Points (structureMap i) b
/-- Exactly the existing arbitrary-Scheme equivalence, now targeting the
proved rational completed-curve group rather than an assumed group object. -/
@[expose] def equiv:Points i b≃RationalSchemePointOperations318.Points
    (publishedA i) (publishedB i) (discriminant_unit i) b:=pointEquiv i b
instance group:AddCommGroup (Points i b):=(equiv i b).addCommGroup
@[expose] def addEquiv:Points i b≃+RationalSchemePointOperations318.Points
    (publishedA i) (publishedB i) (discriminant_unit i) b where
  __:=equiv i b
  map_add' p q:=(equiv i b).apply_symm_apply _
@[simp] theorem addEquiv_val (p:Points i b):(addEquiv i b p).val=
    p.val≫(CompletedNormalizationIso318.iso i).hom:=rfl

/-- The group zero is the previously constructed actual infinity section. -/
theorem zero_eq:(0:Points i b)=CompletedIsoOperations318.pointZero
    (publishedA i) (publishedB i) (CompletedNormalizationIso318.iso i) (structureMap i) (iso_over_Q i) b:=by
  apply (equiv i b).injective
  change (equiv i b) ((equiv i b).symm 0)=_
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (CompletedIsoOperations318.pointZero_comparison _ _ _ _ _ _).symm

theorem neg_eq (p:Points i b):-p=CompletedIsoOperations318.pointNeg
    (publishedA i) (publishedB i) (CompletedNormalizationIso318.iso i) (structureMap i) (iso_over_Q i) b p:=by
  apply (equiv i b).injective
  change (equiv i b) ((equiv i b).symm (-(equiv i b p)))=_
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (CompletedIsoOperations318.pointNeg_comparison _ _ _ _ _ _ _).symm

theorem add_eq (p q:Points i b):p+q=CompletedIsoOperations318.pointSum
    (publishedA i) (publishedB i) (CompletedNormalizationIso318.iso i) (structureMap i) (iso_over_Q i) b (discriminant_unit i) p q:=by
  apply (equiv i b).injective
  change (equiv i b) ((equiv i b).symm ((equiv i b p)+(equiv i b q)))=_
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (CompletedIsoOperations318.pointSum_comparison _ _ _ _ _ _ _ _ _).symm

@[simp] theorem zero_val:(0:Points i b).val=b≫CharacterQuotientOperations318.zero i:=by
  rw [zero_eq]
  rfl
@[simp] theorem neg_val (p:Points i b):(-p).val=p.val≫CharacterQuotientOperations318.negation i:=by
  rw [neg_eq]
  rfl
@[simp] theorem add_val (p q:Points i b):(p+q).val=
    CompletedIsoOperations318.pointPair (structureMap i) b p q≫CharacterQuotientOperations318.addition i:=by
  rw [add_eq]
  rfl

/-- The actual group-valued represented functor, with pullback given by
literal precomposition of Scheme morphisms. -/
@[expose] def precomposeHom {U:Scheme} (f:U⟶T):Points i b→+Points i (f≫b):=
  (addEquiv i (f≫b)).symm.toAddMonoidHom.comp
    ((RationalSchemePointGroup318.precomposeHom (publishedA i) (publishedB i)
      (discriminant_unit i) b f).comp (addEquiv i b).toAddMonoidHom)
@[simp] theorem precomposeHom_val {U:Scheme} (f:U⟶T) (p:Points i b):
    (precomposeHom i b f p).val=f≫p.val:=by
  change (f≫(p.val≫(CompletedNormalizationIso318.iso i).hom))≫
    (CompletedNormalizationIso318.iso i).inv=f≫p.val
  simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id]
end CharacterQuotientPointGroup318
