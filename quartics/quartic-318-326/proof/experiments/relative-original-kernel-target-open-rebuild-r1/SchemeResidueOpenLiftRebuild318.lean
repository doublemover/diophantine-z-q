module
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public section
noncomputable section
namespace SchemeResidueOpenLiftRebuild318
open AlgebraicGeometry CategoryTheory
universe u
variable {X U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j] (f : X ⟶ Y)
  (h : ∀ x : X, ∃ a : Spec (X.residueField x) ⟶ U,
    a ≫ j = X.fromSpecResidueField x ≫ f)
include h in
/-- All actual residue-field tests suffice for an open factorization.
The point is the native residue morphism, not an assumed rational point. -/
lemma range_subset : Set.range f ⊆ Set.range j := by
  rintro _ ⟨x,rfl⟩
  obtain ⟨a,ha⟩ := h x
  let t : Spec (X.residueField x) := closedPoint (X.residueField x)
  refine ⟨a t,?_⟩
  have he := congrArg (fun b : Spec (X.residueField x) ⟶ Y => b t) ha
  simpa only [Scheme.Hom.comp_apply,Scheme.fromSpecResidueField_apply] using he
/-- Native whole-scheme open lift, including the empty source. -/
def lift : X ⟶ U := IsOpenImmersion.lift j f (range_subset j f h)
@[reassoc] lemma lift_fac : lift j f h ≫ j = f := IsOpenImmersion.lift_fac _ _ _
lemma unique (a : X ⟶ U) (ha : a ≫ j = f) : a = lift j f h :=
  (cancel_mono j).mp (ha.trans (lift_fac j f h).symm)
end SchemeResidueOpenLiftRebuild318
