module
public import ContactOriginalIsomGeometricAssociativity318
public section
noncomputable section
namespace WholeSchemeFiberParameterPoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {P B T S S' : Scheme.{u}} (q : P ⟶ B) (t : T ⟶ B) (s : S ⟶ T)
abbrev FiberPoints := {z : S ⟶ pullback q t // z ≫ pullback.snd q t=s}
abbrev OriginalPoints := {z : S ⟶ P // z ≫ q=s ≫ t}
/-- The actual scheme fiber product classifies the SAME whole parameter
maps after arbitrary base change, with every structural map retained. -/
@[expose] def equivalence : FiberPoints q t s ≃ OriginalPoints q t s where
  toFun z := ⟨z.val ≫ pullback.fst q t,by
    rw [Category.assoc,pullback.condition,←Category.assoc,z.property]⟩
  invFun z := ⟨pullback.lift z.val s z.property,pullback.lift_snd _ _ _⟩
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans z.property.symm
  right_inv z := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _
variable (s' : S' ⟶ T) (h : S' ⟶ S) (hh : h ≫ s=s')
@[expose] def fiberMap (z : FiberPoints q t s) : FiberPoints q t s' :=
  ⟨h ≫ z.val,by rw [Category.assoc,z.property,hh]⟩
@[expose] def originalMap (z : OriginalPoints q t s) : OriginalPoints q t s' :=
  ⟨h ≫ z.val,by rw [Category.assoc,z.property,←Category.assoc,hh]⟩
lemma natural (z : FiberPoints q t s) :
    equivalence q t s' (fiberMap q t s s' h hh z)=
      originalMap q t s s' h hh (equivalence q t s z) := by
  apply Subtype.ext
  exact Category.assoc _ _ _
end WholeSchemeFiberParameterPoints318
