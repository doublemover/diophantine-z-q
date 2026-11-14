module
public import FramedZeroVanishingEquivalence318
public section
noncomputable section
namespace FramedZeroArbitraryBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FramedZeroUniversalData318 FramedZeroUniversalLift318
universe u
variable {X T : Scheme.{u}} (D : Data X) (f : T ⟶ X)

/-- The actual categorical base change of the full zero scheme. Neither
flatness nor reducedness of the base is imposed. -/
abbrev scheme := pullback f D.inclusion
abbrev inclusion : scheme D f ⟶ T := pullback.fst f D.inclusion
abbrev toOriginal : scheme D f ⟶ D.Zero := pullback.snd f D.inclusion
instance closed : IsClosedImmersion (inclusion D f) := inferInstance
lemma cartesian : IsPullback (inclusion D f) (toOriginal D f) f D.inclusion :=
  IsPullback.of_hasPullback _ _

/-- Exact FULL kernel-ideal base change, including arbitrary nilpotents
and nonflat tests. Nonzerodivisor preservation is not asserted here. -/
lemma kernel : (inclusion D f).ker=D.inclusion.ker.comap f :=
  Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ _

@[expose] def lift {S : Scheme.{u}} (g : S ⟶ T) (h : D.Vanishing (g≫f)) : S ⟶ scheme D f :=
  pullback.lift g (FramedZeroUniversalLift318.lift D (g≫f) h)
    (FramedZeroUniversalLift318.lift_inclusion D (g≫f) h).symm
@[reassoc] lemma lift_inclusion {S : Scheme.{u}} (g : S ⟶ T) (h : D.Vanishing (g≫f)) :
    lift D f g h≫inclusion D f=g := pullback.lift_fst _ _ _

/-- Arbitrary base change represents literal coefficient vanishing
under composition, as a unique actual scheme lift. -/
theorem existsUnique_lift_iff {S : Scheme.{u}} (g : S ⟶ T) :
    (∃! p : S ⟶ scheme D f,p≫inclusion D f=g) ↔ D.Vanishing (g≫f) := by
  constructor
  · rintro ⟨p,hp,_⟩
    apply vanishing_of_factor D _ (p≫toOriginal D f)
    rw [Category.assoc,←pullback.condition,←Category.assoc,hp]
  · intro h
    refine ⟨lift D f g h,lift_inclusion D f g h,?_⟩
    intro p hp
    apply (cancel_mono (inclusion D f)).1
    rw [lift_inclusion,hp]
end FramedZeroArbitraryBaseChange318
