module
public import ChangedPrimitiveKernel318
public section
noncomputable section
namespace ChangedPrimitiveFunctor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (S:Type) [CommRing S] [Algebra (OpenJModel318.Base N) S]
local notation "R" => OpenJModel318.Base N
local notation "a" => algebraMap R S
local notation "A" => a (OpenJAffineScheme318.A N)
local notation "B" => a (OpenJAffineScheme318.B N)
local notation "hD" => CompletedKernelBaseChange318.mappedDiscriminant (S:=S)
  (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
variable [Invertible (3:S)]
local notation "E" => WeierstrassGluing318.scheme A B
local notation "T" => ThreeTorsionScheme318.scheme A B hD
local notation "ι" => ThreeTorsionCompletedDoubling318.inclusion A B hD

@[expose] def Points (X:Scheme) := {t:X ⟶ E //
  (t ≫ CompletedIteratedAddition318.tripling A B hD=
    t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B) ∧
    ChangedPrimitiveKernel318.NowhereZero N S t}

/-- Both inverse witnesses concern the actual original inclusion with mapped coefficients. -/
@[expose] def equivalence (X:Scheme) : (X ⟶ T) ≃ Points N S X where
  toFun g:=⟨g ≫ ι,(ChangedPrimitiveKernel318.exists_iff N S _).mp ⟨g,rfl⟩⟩
  invFun t:=(ChangedPrimitiveKernel318.universal N S t.val t.property.1 t.property.2).choose
  left_inv g:=by
    exact (ChangedPrimitiveKernel318.universal N S (g ≫ ι)
      ((ChangedPrimitiveKernel318.exists_iff N S _).mp ⟨g,rfl⟩).1
      ((ChangedPrimitiveKernel318.exists_iff N S _).mp ⟨g,rfl⟩).2).choose_spec.2 g rfl |>.symm
  right_inv t:=by
    apply Subtype.ext
    exact (ChangedPrimitiveKernel318.universal N S t.val t.property.1 t.property.2).choose_spec.1
@[simp] theorem equivalence_val {X:Scheme} (g:X ⟶ T) : (equivalence N S X g).val=g ≫ ι := rfl

@[expose] def precomp {X Y:Scheme} (f:X ⟶ Y) (t:Points N S Y) : Points N S X :=
  ⟨f ≫ t.val,by
    constructor
    · simpa only [Category.assoc] using congrArg (fun k=>f ≫ k) t.property.1
    · intro x
      exact t.property.2 (f x)⟩
theorem natural {X Y:Scheme} (f:X ⟶ Y) (g:Y ⟶ T) :
    equivalence N S X (f ≫ g)=precomp N S f (equivalence N S Y g) := by
  apply Subtype.ext
  exact Category.assoc f g ι
end ChangedPrimitiveFunctor318
