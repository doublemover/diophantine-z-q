module
public import FramedZeroUniversalLift318
public section
noncomputable section
namespace FramedZeroVanishingEquivalence318
open AlgebraicGeometry CategoryTheory
open FramedZeroUniversalData318 FramedZeroUniversalLift318
universe u
variable {X : Scheme.{u}} (D : Data X)
@[expose] def VanishingMaps (T : Scheme.{u}) := {f : T ⟶ X // D.Vanishing f}

/-- BOTH-INVERSE representation of the actual vanishing subfunctor on
ALL scheme tests; no reducedness, finite type or C-point restriction. -/
@[expose] def equivalence (T : Scheme.{u}) : (T ⟶ D.Zero) ≃ VanishingMaps D T where
  toFun g := ⟨g≫D.inclusion,vanishing_of_factor D _ g rfl⟩
  invFun f := lift D f.val f.property
  left_inv g := by
    apply (cancel_mono D.inclusion).1
    exact lift_inclusion D _ _
  right_inv f := Subtype.ext (lift_inclusion D _ _)

lemma vanishing_comp {S T : Scheme.{u}} (a : S ⟶ T) (f : T ⟶ X) (h : D.Vanishing f) :
    D.Vanishing (a≫f) := by
  apply vanishing_of_factor D _ (a≫lift D f h)
  rw [Category.assoc,lift_inclusion]
@[expose] def precomp {S T : Scheme.{u}} (a : S ⟶ T) : VanishingMaps D T → VanishingMaps D S :=
  fun f => ⟨a≫f.val,vanishing_comp D a f.val f.property⟩
lemma naturality {S T : Scheme.{u}} (a : S ⟶ T) (g : T ⟶ D.Zero) :
    equivalence D S (a≫g)=precomp D a (equivalence D T g) := by
  apply Subtype.ext
  exact Category.assoc _ _ _
lemma lift_naturality {S T : Scheme.{u}} (a : S ⟶ T) (f : VanishingMaps D T) :
    (equivalence D S).symm (precomp D a f)=a≫(equivalence D T).symm f := by
  apply (cancel_mono D.inclusion).1
  change lift D _ _≫D.inclusion=(a≫lift D f.val f.property)≫D.inclusion
  rw [lift_inclusion,Category.assoc,lift_inclusion]
end FramedZeroVanishingEquivalence318
