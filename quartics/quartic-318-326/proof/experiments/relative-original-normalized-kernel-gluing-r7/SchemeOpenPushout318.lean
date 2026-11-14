module
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace SchemeOpenPushout318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {U X Y : Scheme.{u}} (f : U ⟶ X) (g : U ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]
instance inl_open : IsOpenImmersion (pushout.inl f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.left))
instance inr_open : IsOpenImmersion (pushout.inr f g) :=
  inferInstanceAs (IsOpenImmersion (colimit.ι (span f g) WalkingSpan.right))
lemma intersection : (pushout.inr f g) ⁻¹ᵁ (pushout.inl f g).opensRange=g.opensRange := by
  ext y
  change (∃ x, pushout.inl f g x=pushout.inr f g y) ↔ ∃ z, g z=y
  constructor
  · rintro ⟨x,hxy⟩
    obtain ⟨k,ki,kj,z,hx,hy⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (span f g)).mp hxy
    cases k with
    | none =>
      have hi : ki=WalkingSpan.Hom.fst := Subsingleton.elim _ _
      have hj : kj=WalkingSpan.Hom.snd := Subsingleton.elim _ _
      subst ki
      subst kj
      exact ⟨z,hy⟩
    | some k =>
      cases k with
      | left => cases kj
      | right => cases ki
  · rintro ⟨z,rfl⟩
    refine ⟨f z,?_⟩
    exact congrArg (fun k : U ⟶ pushout f g => k z) (pushout.condition (f := f) (g := g))
/-- Gluing along two actual open immersions retains their whole original
intersection as a categorical pullback. -/
lemma cartesian : IsPullback f g (pushout.inl f g) (pushout.inr f g) :=
  IsOpenImmersion.isPullback f g (pushout.inl f g) (pushout.inr f g)
    (pushout.condition (f := f) (g := g)).symm (intersection f g)
lemma jointly_surjective (z : pushout f g) :
    (∃ x, pushout.inl f g x=z) ∨ ∃ y, pushout.inr f g y=z := by
  obtain ⟨i,x,hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) z
  cases i with
  | none =>
    left
    refine ⟨f x,?_⟩
    have h := congrArg (fun k : U ⟶ pushout f g => k x)
      (colimit.w (span f g) WalkingSpan.Hom.fst)
    exact h.trans hx
  | some i =>
    cases i with
    | left => exact Or.inl ⟨x,hx⟩
    | right => exact Or.inr ⟨x,hx⟩
@[expose] def cover : (pushout f g).OpenCover where
  I₀ := Bool
  X b := if b then Y else X
  f b := by cases b; exact pushout.inl f g; exact pushout.inr f g
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro z
      rcases jointly_surjective f g z with ⟨x,hx⟩|⟨y,hy⟩
      · exact ⟨false,x,hx⟩
      · exact ⟨true,y,hy⟩
    · intro b
      cases b <;> infer_instance
end SchemeOpenPushout318
