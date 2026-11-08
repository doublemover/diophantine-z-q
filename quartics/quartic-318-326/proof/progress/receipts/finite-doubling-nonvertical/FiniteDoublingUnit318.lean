module
public import FiniteLocalZero318
public import CompletedAdditionInverse318
public import CompletedIteratedAddition318
public import SpecAlgHomComposition318
public import Mathlib.RingTheory.Ideal.Nonunits
public section
noncomputable section
namespace FiniteDoublingUnit318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Only the actual inverse diagram is used, not associativity or a group-object premise. -/
theorem self_neg_double_zero {X:Scheme.{u}} (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (t:X ⟶ WeierstrassGluing318.scheme A B) (hn:t ≫ GluedNegation318.negation A B=t) :
    t ≫ CompletedIteratedAddition318.doubling A B hD=
      t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B := by
  have he:t ≫ CompletedIteratedAddition318.diagonal A B=t ≫ CompletedAdditionInverse318.antiDiagonal A B := by
    apply pullback.hom_ext
    · simp only [Category.assoc,CompletedIteratedAddition318.diagonal_fst,
        CompletedAdditionInverse318.antiDiagonal_fst,Category.comp_id]
    · simpa only [Category.assoc,CompletedIteratedAddition318.diagonal_snd,
        CompletedAdditionInverse318.antiDiagonal_snd,Category.comp_id] using hn.symm
  rw [CompletedIteratedAddition318.doubling,←Category.assoc,he,Category.assoc,
    CompletedAdditionInverse318.antiDiagonal_addition]

@[expose] def finiteInput (A B:R) (f:ShortAffineJacobian318.Ring A B →ₐ[R] S) :
    Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B :=
  Spec.map (CommRingCat.ofHom f.toRingHom) ≫ WeierstrassGluing318.finiteChart A B
lemma finiteInput_base (A B:R) (f:ShortAffineJacobian318.Ring A B →ₐ[R] S) :
    finiteInput A B f ≫ WeierstrassGluing318.structureMap A B=Spec.algebraMap R S := by
  rw [finiteInput,Category.assoc,WeierstrassGluing318.finiteChart_structure]
  dsimp only [ShortAffineScheme318.structureMap,Spec.algebraMap]
  rw [←Spec.map_comp]
  exact congrArg (fun q=>Spec.map (CommRingCat.ofHom q)) f.comp_algebraMap

lemma self_neg (A B:R) (f:ShortAffineJacobian318.Ring A B →ₐ[R] S)
    (hy:2*f (ShortAffineJacobian318.y A B)=0) :
    finiteInput A B f ≫ GluedNegation318.negation A B=finiteInput A B f := by
  have hf:f.comp (ChartNegation318.affineNeg A B)=f := by
    apply AffineEquationFunctor318.hom_ext
    · simp only [AlgHom.comp_apply,ChartNegation318.affineNeg_x]
    · simp only [AlgHom.comp_apply,ChartNegation318.affineNeg_y,map_neg]
      linear_combination -hy
  rw [finiteInput,Category.assoc,GluedNegation318.finiteChart_negation,←Category.assoc]
  change (Spec.map _ ≫ Spec.map (CommRingCat.ofHom (ChartNegation318.affineNeg A B).toRingHom)) ≫ _=_
  rw [SpecAlgHomComposition318.map_comp,hf]

lemma zero_ordinate_subsingleton (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:ShortAffineJacobian318.Ring A B →ₐ[R] S)
    (h:finiteInput A B f ≫ CompletedIteratedAddition318.doubling A B hD=finiteInput A B g)
    (hy:2*f (ShortAffineJacobian318.y A B)=0) : Subsingleton S := by
  have hz:=self_neg_double_zero A B hD (finiteInput A B f) (self_neg A B f hy)
  rw [h,←Category.assoc,finiteInput_base] at hz
  exact FiniteLocalZero318.finite_zero_subsingleton A B g hz

/-- If an actual finite point has an actual finite doubled output, then 2y
is a unit in the whole test algebra, including all nilpotent directions.
Maximal quotients are used only to detect invertibility, never to infer
an equality of Scheme morphisms. -/
theorem two_y_unit (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (f g:ShortAffineJacobian318.Ring A B →ₐ[R] S)
    (h:finiteInput A B f ≫ CompletedIteratedAddition318.doubling A B hD=finiteInput A B g) :
    IsUnit (2*f (ShortAffineJacobian318.y A B)) := by
  by_contra hn
  obtain ⟨m,hm,hy⟩:=exists_max_ideal_of_mem_nonunits hn
  letI : m.IsMaximal:=hm
  let q:S →ₐ[R] S ⧸ m:=Ideal.Quotient.mkₐ R m
  have hz:2*(q.comp f) (ShortAffineJacobian318.y A B)=0 := by
    have hq:q (2*f (ShortAffineJacobian318.y A B))=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hy
    simpa only [map_mul,map_ofNat,AlgHom.comp_apply] using hq
  have hq:finiteInput A B (q.comp f) ≫ CompletedIteratedAddition318.doubling A B hD=
      finiteInput A B (q.comp g) := by
    have hh:=congrArg (fun k=>Spec.map (CommRingCat.ofHom q.toRingHom) ≫ k) h
    simpa only [finiteInput,←Category.assoc,SpecAlgHomComposition318.map_comp] using hh
  haveI : Subsingleton (S ⧸ m):=zero_ordinate_subsingleton A B hD (q.comp f) (q.comp g) hq hz
  exact zero_ne_one (Subsingleton.elim (0:S ⧸ m) 1)
end FiniteDoublingUnit318
