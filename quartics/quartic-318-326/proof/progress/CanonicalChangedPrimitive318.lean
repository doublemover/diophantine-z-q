module
public import ChangedPrimitiveFunctor318
public section
noncomputable section
namespace CanonicalChangedPrimitive318
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
local notation "E" => WeierstrassGluing318.scheme A B

/-- The exact mapped-coefficient primitive Scheme, with inverse of three
supplied by the literal base rather than imposed as an additional hypothesis. -/
@[expose] def scheme : Scheme := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionScheme318.scheme A B hD
@[expose] def inclusion : scheme N S ⟶ E := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionCompletedDoubling318.inclusion A B hD
@[expose] def structureMap : scheme N S ⟶ Spec (CommRingCat.of S) := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionScheme318.structureMap A B hD

@[reassoc] theorem inclusion_base : inclusion N S ≫ WeierstrassGluing318.structureMap A B=structureMap N S := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionCompletedDoubling318.inclusion_over_base A B hD

theorem universal {X:Scheme} (t:X ⟶ E)
    (h:t ≫ CompletedIteratedAddition318.tripling A B hD=
      t ≫ WeierstrassGluing318.structureMap A B ≫ WeierstrassGluing318.infinity A B)
    (hn:ChangedPrimitiveKernel318.NowhereZero N S t) :
    ∃!g:X ⟶ scheme N S,g ≫ inclusion N S=t := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ChangedPrimitiveKernel318.universal N S t h hn

@[expose] def equivalence (X:Scheme) : (X ⟶ scheme N S) ≃ ChangedPrimitiveFunctor318.Points N S X := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ChangedPrimitiveFunctor318.equivalence N S X
@[simp] theorem equivalence_val {X:Scheme} (g:X ⟶ scheme N S) :
    (equivalence N S X g).val=g ≫ inclusion N S := rfl

theorem natural {X Y:Scheme} (f:X ⟶ Y) (g:Y ⟶ scheme N S) :
    equivalence N S X (f ≫ g)=ChangedPrimitiveFunctor318.precomp N S f (equivalence N S Y g) := by
  apply Subtype.ext
  exact Category.assoc f g (inclusion N S)

theorem finite_etale : IsFinite (structureMap N S) ∧ Etale (structureMap N S) := by
  letI:=ChangedPrimitiveKernel318.inverse_three N S
  exact ThreeTorsionScheme318.finite_etale A B hD
end CanonicalChangedPrimitive318
