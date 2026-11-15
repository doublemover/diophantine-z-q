module
public import TwoOpenAdditiveCocycle318
public import AffineCoverHOneQuotient318
public section
noncomputable section
namespace AffineHOnePointedDeformation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open InfinitesimalUnitCocycle318 TwoOpenAdditiveCocycle318 DualNumberScheme318
set_option maxHeartbeats 1100000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ base R) (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : U ⊔ V = ⊤)
/-- The original two-open cover pulled to the actual dual-number fiber product. -/
@[expose] def thickOpens (a : Bool) : (thickening R p).Opens :=
  (pullback.fst p (structureMap R)) ⁻¹ᵁ opens U V a
omit [IsIntegral X] in
include h in
lemma thick_cover : (⊤ : (thickening R p).Opens) ≤ ⨆ a, thickOpens p U V a :=
  LinePullbackFrames318.preimage_cover _ _ (cover U V h)
/-- Actual overlap functions are first pulled by the actual first projection,
then exponentiated using the actual epsilon, on the full actual cover. -/
@[expose] def representativeClass (x : Γ(X,U ⊓ V)) : DualNumberScheme318.Class R p :=
  AdditiveDeformationClasses318.dualNumberClasses p (thickOpens p U V) (thick_cover p U V h)
    (AdditiveCocycleRefinement318.classes (pullback.fst p (structureMap R))
      (opens U V) (thickOpens p U V) (fun _ => le_rfl)
      (Quotient.mk _ (TwoOpenAdditiveCocycle318.cocycle U V x)))
/-- Equality in the ORIGINAL H1 gives the original finite-minus-infinity
coboundary, and hence an isomorphism preserving the ACTUAL special-fiber frame. -/
lemma representative_independent (x y : Γ(X,U ⊓ V))
    (hxy : AffineCoverHOnePresentation318.boundary U V h x =
      AffineCoverHOnePresentation318.boundary U V h y) :
    representativeClass p U V h x = representativeClass p U V h y := by
  have hz : AffineCoverHOnePresentation318.boundary U V h (y - x) = 0 := by
    rw [map_sub, ← hxy, sub_self]
  have hk := (AffineCoverHOneQuotient318.kernel_eq_range U V h)
  have hm : y - x ∈ (AffineCoverHOneQuotient318.difference U V).range := by
    rw [← hk]
    exact hz
  obtain ⟨⟨a,b⟩,hab⟩ := hm
  have hy : y = restrict X inf_le_left a - restrict X inf_le_right b + x := by
    change restrict X inf_le_left a - restrict X inf_le_right b = y - x at hab
    rw [hab]
    abel
  have he : (Quotient.mk (AdditiveDeformationClasses318.additiveSetoid X (opens U V))
      (TwoOpenAdditiveCocycle318.cocycle U V x)) =
    Quotient.mk _ (TwoOpenAdditiveCocycle318.cocycle U V y) :=
    Quotient.sound (TwoOpenAdditiveCocycle318.coboundary U V x y a b hy)
  exact congrArg (fun c => AdditiveDeformationClasses318.dualNumberClasses p
    (thickOpens p U V) (thick_cover p U V h)
    (AdditiveCocycleRefinement318.classes (pullback.fst p (structureMap R))
      (opens U V) (thickOpens p U V) (fun _ => le_rfl) c)) he
/-- A chosen representative is only an implementation device: the next theorem
proves the original boundary formula for EVERY representative. -/
@[expose] def representative (z : SheafCohomologyRetraction318.structureH X 1) : Γ(X,U ⊓ V) :=
  (AffineCoverHOnePresentation318.boundary_surjective U V hU hV h z).choose
lemma representative_boundary (z : SheafCohomologyRetraction318.structureH X 1) :
    AffineCoverHOnePresentation318.boundary U V h (representative U V hU hV h z) = z :=
  (AffineCoverHOnePresentation318.boundary_surjective U V hU hV h z).choose_spec
/-- Original global H1 classes give actual pointed line deformations on the
actual dual-number thickening. No classification or injectivity is assumed. -/
@[expose] def map : SheafCohomologyRetraction318.structureH X 1 → DualNumberScheme318.Class R p :=
  fun z => representativeClass p U V h (representative U V hU hV h z)
lemma map_boundary (x : Γ(X,U ⊓ V)) :
    map p U V hU hV h (AffineCoverHOnePresentation318.boundary U V h x) =
      representativeClass p U V h x :=
  representative_independent p U V h _ x
    (representative_boundary U V hU hV h (AffineCoverHOnePresentation318.boundary U V h x))
end AffineHOnePointedDeformation318
