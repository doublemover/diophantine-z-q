module
public import LiteralIndependentPairOpen318
public section
noncomputable section
namespace LiteralIndependentPairFunctor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelAddition318 LiteralIndependentPairOpen318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
/-- The represented functor keeps every residue-field independence test,
not merely inequalities between the two global sections. -/
@[expose] def Points (X:Scheme):={f:X ⟶ product N // FiberwiseIndependent N f}
@[expose] def equivalence (X:Scheme) : (X ⟶ scheme N) ≃ Points N X where
  toFun g:=⟨g ≫ inclusion N,(exists_iff N _).mp ⟨g,rfl⟩⟩
  invFun p:=(universal N p.val p.property).choose
  left_inv g:=by
    exact ((universal N (g ≫ inclusion N) ((exists_iff N _).mp ⟨g,rfl⟩)).choose_spec.2 g rfl).symm
  right_inv p:=by
    apply Subtype.ext
    exact (universal N p.val p.property).choose_spec.1
@[simp] theorem equivalence_val {X:Scheme} (g:X ⟶ scheme N) :
    (equivalence N X g).val=g ≫ inclusion N:=rfl

/-- Fiberwise independence is preserved under arbitrary Scheme pullback,
proved through its actual open representability, without a reducedness
assumption or a global-inequality substitution. -/
theorem precompose_independent {X Y:Scheme} (f:X ⟶ Y) (g:Y ⟶ product N)
    (h:FiberwiseIndependent N g) : FiberwiseIndependent N (f ≫ g):=by
  obtain ⟨k,hk⟩:=(universal N g h).exists
  apply (exists_iff N _).mp
  exact ⟨f ≫ k,by rw [Category.assoc,hk]⟩
@[expose] def precompose {X Y:Scheme} (f:X ⟶ Y) (p:Points N Y) : Points N X:=
  ⟨f ≫ p.val,precompose_independent N f p.val p.property⟩
theorem natural {X Y:Scheme} (f:X ⟶ Y) (g:Y ⟶ scheme N) :
    equivalence N X (f ≫ g)=precompose N f (equivalence N Y g):=by
  apply Subtype.ext
  exact Category.assoc f g (inclusion N)

/-- Exact two original kernel projections of every represented pair. -/
@[expose] def first : scheme N ⟶ ThreeTorsionTriplingFiber318.fiber (OpenJAffineScheme318.A N)
    (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N):=
  inclusion N ≫ pullback.fst (LiteralKernelSchemePoints318.structureMap N) (LiteralKernelSchemePoints318.structureMap N)
@[expose] def second : scheme N ⟶ ThreeTorsionTriplingFiber318.fiber (OpenJAffineScheme318.A N)
    (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N):=
  inclusion N ≫ pullback.snd (LiteralKernelSchemePoints318.structureMap N) (LiteralKernelSchemePoints318.structureMap N)
@[reassoc] theorem first_base : first N ≫ LiteralKernelSchemePoints318.structureMap N=
    second N ≫ LiteralKernelSchemePoints318.structureMap N:=by
  simp only [first,second,Category.assoc,pullback.condition]
@[reassoc] theorem equivalence_first {X:Scheme} (g:X ⟶ scheme N) :
    (equivalence N X g).val ≫ pullback.fst (LiteralKernelSchemePoints318.structureMap N)
      (LiteralKernelSchemePoints318.structureMap N)=g ≫ first N:=Category.assoc _ _ _
@[reassoc] theorem equivalence_second {X:Scheme} (g:X ⟶ scheme N) :
    (equivalence N X g).val ≫ pullback.snd (LiteralKernelSchemePoints318.structureMap N)
      (LiteralKernelSchemePoints318.structureMap N)=g ≫ second N:=Category.assoc _ _ _
end LiteralIndependentPairFunctor318
