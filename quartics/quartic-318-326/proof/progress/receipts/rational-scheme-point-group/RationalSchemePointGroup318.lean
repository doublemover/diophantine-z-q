module
public import RationalSchemePointAssociativity318
public section
noncomputable section
namespace RationalSchemePointGroup318
open AlgebraicGeometry CategoryTheory
open RationalSchemePointOperations318 RationalSchemePointAssociativity318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (A B:ℚ) (hD:IsUnit (-16*(4*A^3+27*B^2))) {T:Scheme}
variable (b:T ⟶ Spec (CommRingCat.of ℚ))

instance : Add (Points A B hD b) := ⟨sum A B hD b⟩
instance : Zero (Points A B hD b) := ⟨RationalSchemePointOperations318.zero A B hD b⟩
instance : Neg (Points A B hD b) := ⟨neg A B hD b⟩

/-- The actual represented points over every Scheme test form an abelian group;
the operations are precisely the already checked Scheme morphisms. -/
instance group : AddCommGroup (Points A B hD b) where
  add := sum A B hD b
  zero := RationalSchemePointOperations318.zero A B hD b
  neg := neg A B hD b
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := sum_assoc A B hD b
  zero_add := zero_sum A B hD b
  add_zero := sum_zero A B hD b
  neg_add_cancel := neg_sum A B hD b
  add_comm := sum_comm A B hD b

lemma neg_sum (p q:Points A B hD b) :
    neg A B hD b (sum A B hD b p q)=sum A B hD b (neg A B hD b p) (neg A B hD b q) := neg_add p q
lemma neg_triple (p:Points A B hD b) :
    neg A B hD b (sum A B hD b (sum A B hD b p p) p)=
      sum A B hD b (sum A B hD b (neg A B hD b p) (neg A B hD b p)) (neg A B hD b p) := by
  rw [neg_sum,neg_sum]

/-- Arbitrary Scheme pullback acts on the actual group functor by the
actual composition of Scheme maps. -/
@[expose] def precompose {U:Scheme} (f:U ⟶ T) (p:Points A B hD b) : Points A B hD (f ≫ b):=
  ⟨f ≫ p.val,by rw [Category.assoc,p.property]⟩
lemma precompose_pair {U:Scheme} (f:U ⟶ T) (p q:Points A B hD b) :
    pair A B hD (f ≫ b) (precompose A B hD b f p) (precompose A B hD b f q)=f ≫ pair A B hD b p q:=by
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [pair_fst,Category.assoc,pair_fst];rfl
  · rw [pair_snd,Category.assoc,pair_snd];rfl
@[expose] def precomposeHom {U:Scheme} (f:U ⟶ T) : Points A B hD b →+ Points A B hD (f ≫ b) where
  toFun:=precompose A B hD b f
  map_zero':=by
    apply Subtype.ext
    change f ≫ (b ≫ WeierstrassGluing318.infinity A B)=(f ≫ b) ≫ WeierstrassGluing318.infinity A B
    exact (Category.assoc f b (WeierstrassGluing318.infinity A B)).symm
  map_add' p q:=by
    apply Subtype.ext
    change f ≫ (pair A B hD b p q ≫ CompletedAddition318.addition A B hD)=
      pair A B hD (f ≫ b) (precompose A B hD b f p) (precompose A B hD b f q) ≫ CompletedAddition318.addition A B hD
    rw [precompose_pair,Category.assoc]
@[simp] theorem zero_val : (0:Points A B hD b).val=b ≫ WeierstrassGluing318.infinity A B:=rfl
@[simp] theorem neg_val (p:Points A B hD b) : (-p).val=p.val ≫ GluedNegation318.negation A B:=rfl
@[simp] theorem add_val (p q:Points A B hD b) : (p+q).val=
    pair A B hD b p q ≫ CompletedAddition318.addition A B hD:=rfl
@[simp] theorem precomposeHom_val {U:Scheme} (f:U ⟶ T) (p:Points A B hD b) :
    (precomposeHom A B hD b f p).val=f ≫ p.val:=rfl
end RationalSchemePointGroup318
