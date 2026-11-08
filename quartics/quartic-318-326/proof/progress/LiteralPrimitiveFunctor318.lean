module
public import LiteralPrimitiveKernel318
public section
noncomputable section
namespace LiteralPrimitiveFunctor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "E" => WeierstrassGluing318.literalScheme N
local notation "T" => ThreeTorsionScheme318.scheme A B hD
local notation "ι" => ThreeTorsionCompletedDoubling318.inclusion A B hD

/-- Actual nowhere-zero, tripling-killed Scheme-valued points. -/
@[expose] def Points (X:Scheme) := {t:X ⟶ E //
  (t ≫ CompletedIteratedAddition318.tripling A B hD=
    t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B) ∧
    LiteralPrimitiveKernel318.NowhereZero N t}

@[expose] def equivalence (X:Scheme) : (X ⟶ T) ≃ Points N X where
  toFun g:=⟨g ≫ ι,(LiteralPrimitiveKernel318.exists_iff N _).mp ⟨g,rfl⟩⟩
  invFun t:=(LiteralPrimitiveKernel318.universal N t.val t.property.1 t.property.2).choose
  left_inv g:=by
    exact (LiteralPrimitiveKernel318.universal N (g ≫ ι)
      ((LiteralPrimitiveKernel318.exists_iff N _).mp ⟨g,rfl⟩).1
      ((LiteralPrimitiveKernel318.exists_iff N _).mp ⟨g,rfl⟩).2).choose_spec.2 g rfl |>.symm
  right_inv t:=by
    apply Subtype.ext
    exact (LiteralPrimitiveKernel318.universal N t.val t.property.1 t.property.2).choose_spec.1

@[simp] theorem equivalence_val {X:Scheme} (g:X ⟶ T) :
    (equivalence N X g).val=g ≫ ι := rfl

@[expose] def precomp {X Y:Scheme} (f:X ⟶ Y) (t:Points N Y) : Points N X :=
  ⟨f ≫ t.val,by
    constructor
    · simpa only [Category.assoc] using congrArg (fun k=>f ≫ k) t.property.1
    · intro x
      exact t.property.2 (f x)⟩

/-- The representability equivalence uses the actual inclusion and commutes
with arbitrary Scheme precomposition, not just maps of fields. -/
theorem natural {X Y:Scheme} (f:X ⟶ Y) (g:Y ⟶ T) :
    equivalence N X (f ≫ g)=precomp N f (equivalence N Y g) := by
  apply Subtype.ext
  exact Category.assoc f g ι
end LiteralPrimitiveFunctor318
