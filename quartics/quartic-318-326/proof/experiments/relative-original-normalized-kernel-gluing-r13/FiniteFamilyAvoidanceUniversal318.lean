module
public import FiniteFamilyAvoidanceIntersections318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace FiniteFamilyAvoidanceUniversal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FiniteFamilyAvoidanceOpen318 FiniteFamilyAvoidanceFactor318
universe u
variable {Z B X : Scheme.{u}} (p : Z ⟶ B) [UniversallyClosed p] (q : Z ⟶ X) (U : X.Opens)
abbrev family := pullback p (locus p q U).ι
abbrev intoFamily : family p q U ⟶ Z := pullback.fst p (locus p q U).ι
abbrev projection : family p q U ⟶ (locus p q U).toScheme := pullback.snd p (locus p q U).ι
lemma supported : Supported p q U (locus p q U).ι := by
  simpa only [Category.id_comp] using supported_comp p q U (𝟙 (locus p q U).toScheme)
/-- The WHOLE restricted universal family factors through the original
source open, retaining its actual coefficient-base-change construction. -/
@[expose] def intoSource : family p q U ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (intoFamily p q U ≫ q) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z,rfl⟩
    exact supported p q U z)
@[reassoc] lemma intoSource_into : intoSource p q U ≫ U.ι=intoFamily p q U ≫ q :=
  IsOpenImmersion.lift_fac _ _ _
lemma cartesian : IsPullback (intoFamily p q U) (projection p q U) p (locus p q U).ι :=
  IsPullback.of_hasPullback p (locus p q U).ι
instance finite [IsFinite p] : IsFinite (projection p q U) := inferInstance
instance flat [Flat p] : Flat (projection p q U) := inferInstance
end FiniteFamilyAvoidanceUniversal318
