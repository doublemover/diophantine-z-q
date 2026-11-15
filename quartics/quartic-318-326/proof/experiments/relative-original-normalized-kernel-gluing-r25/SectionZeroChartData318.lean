module
public import CartierCanonicalSectionIdeal318
public section
noncomputable section
namespace SectionZeroChartData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) (L : Line X) (s : Γ(L.object,⊤))
/-- Complete actual affine quotient charts for the zero scheme of the
specified global section of the specified original line. -/
structure Data where
  Index : Type u
  ring : Index → CommRingCat.{u}
  into : ∀ i,Spec (ring i) ⟶ X
  [open_into : ∀ i,IsOpenImmersion (into i)]
  cover : ⊤≤⨆i,(into i).opensRange
  zero : ∀ i,Spec (CommRingCat.of (ring i ⧸ SectionZeroAffineRefinement318.sectionIdeal (ring i) (into i) L s)) ⟶ Z
  cartesian : ∀ i,IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (SectionZeroAffineRefinement318.sectionIdeal (ring i) (into i) L s)))) (zero i) (into i) p
attribute [instance] Data.open_into
end SectionZeroChartData318
