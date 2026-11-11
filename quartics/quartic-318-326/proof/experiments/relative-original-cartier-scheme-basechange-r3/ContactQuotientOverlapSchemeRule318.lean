module
public import RelativeAffineTestIso318
public import ContactQuotientOpenPointNaturality318
public section
noncomputable section
namespace ContactQuotientOverlapSchemeRule318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
abbrev scheme := (parameterOpen c a b n).toScheme
@[expose] def structureMap : scheme c a b n ⟶ Spec (CommRingCat.of ℚ) :=
  (parameterOpen c a b n).ι ≫ VaryingWordParameterStructure318.structureMap ℚ (ring c a) (Fin n)
/-- The prior open-point functor is exactly the relative affine-test
functor of this ACTUAL open scheme. -/
@[expose] def pointTest (S : CommRingCat.{0}) [Algebra ℚ S] :
    Point c a b n S ≃ RelativeAffineTestRule318.Test ℚ (structureMap c a b n) S where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- The actual chart-transfer operation supplies every coefficient test
of the genuine overlap schemes, naturally in every algebra map. -/
@[expose] def rule : RelativeAffineTestRule318.Rule ℚ (structureMap c a b n) (structureMap c b a n) where
  app S _ x := pointTest c b a n S
    (ContactQuotientOverlapPointEquiv318.transition c a b n S ((pointTest c a b n S).symm x))
  natural S T _ _ φ x := by
    apply Subtype.ext
    exact congrArg Subtype.val (ContactQuotientOpenPointNaturality318.transition_natural c a b n S T φ
      ((pointTest c a b n S).symm x))
end ContactQuotientOverlapSchemeRule318
