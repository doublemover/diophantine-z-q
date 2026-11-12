module
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace GenericOpenPushout318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U X Y:Scheme.{u}} (f:U ⟶ X) (g:U ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion g]
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
/-- A point equality in the actual pushout of two open immersions is witnessed
by a point of their original common open. -/
theorem exists_overlap (x:X) (y:Y) (h:pushout.inl f g x=pushout.inr f g y) :
    ∃z:U, f z=x ∧ g z=y := by
  obtain ⟨k,ki,kj,z,h1,h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff
    (span f g) (i:=WalkingSpan.left) (j:=WalkingSpan.right) (xi:=x) (xj:=y)).mp h
  cases k with
  | none =>
    cases ki
    cases kj
    exact ⟨z,h1,h2⟩
  | some k =>
    cases k with
    | left => cases kj
    | right => cases ki
/-- The pushout square of two Scheme open immersions is also their actual
categorical intersection square. -/
theorem square : IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback g f (pushout.inr f g) (pushout.inl f g)
  · exact pushout.condition
  · ext x
    change (pushout.inl f g x ∈ Set.range (pushout.inr f g)) ↔ x ∈ Set.range f
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨z,hz,_⟩ := exists_overlap f g x y hy.symm
      exact ⟨z,hz⟩
    · rintro ⟨z,rfl⟩
      refine ⟨g z,?_⟩
      exact congrArg (fun h=>h z) (pushout.condition (f:=f) (g:=g)).symm
end GenericOpenPushout318
