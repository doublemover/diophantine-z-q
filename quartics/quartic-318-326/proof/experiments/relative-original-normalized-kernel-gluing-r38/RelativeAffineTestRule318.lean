module
public import AffineSchemeAlgebraMap318
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace RelativeAffineTestRule318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of R)) (q : Y ⟶ Spec (CommRingCat.of R))
abbrev Test (S : CommRingCat.{u}) [Algebra R S] :=
  {f : Spec S ⟶ X // f ≫ p=VaryingSourceCoefficientPullback318.base R S}
@[expose] def map (S T : CommRingCat.{u}) [Algebra R S] [Algebra R T]
    (φ : S →ₐ[R] T) (x : Test R p S) : Test R p T :=
  ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val,by
    rw [Category.assoc,x.property]
    exact VaryingSourceCoefficientPullback318.coefficient_base R S T φ⟩
/-- A natural transformation on ALL affine coefficient tests. It does
not assume a realizing scheme map or that either scheme is affine. -/
structure Rule where
  app : ∀ (S : CommRingCat.{u}) [Algebra R S], Test R p S → Test R q S
  natural : ∀ (S T : CommRingCat.{u}) [Algebra R S] [Algebra R T]
    (φ : S →ₐ[R] T) (x : Test R p S),
    app T (map R p S T φ x)=map R q S T φ (app S x)
variable (F : Rule R p q)
/-- Naturality along an arbitrary ACTUAL affine scheme map, converted
using its actual structure-map equality, not a guessed algebra map. -/
lemma on_arrow (S T : CommRingCat.{u}) [Algebra R S] [Algebra R T]
    (g : Spec T ⟶ Spec S) (hg : g ≫ VaryingSourceCoefficientPullback318.base R S=
      VaryingSourceCoefficientPullback318.base R T)
    (x : Test R p S) (y : Test R p T) (h : g ≫ x.val=y.val) :
    (F.app T y).val=g ≫ (F.app S x).val := by
  let φ := AffineSchemeAlgebraMap318.hom R S T g hg
  have hφ : Spec.map (CommRingCat.ofHom φ.toRingHom)=g := AffineSchemeAlgebraMap318.spec_hom R S T g hg
  have hx : map R p S T φ x=y := by apply Subtype.ext; change Spec.map _ ≫ x.val=y.val; rw [hφ,h]
  have hn := congrArg Subtype.val (F.natural S T φ x)
  rw [hx] at hn
  change (F.app T y).val=Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (F.app S x).val at hn
  rw [hφ] at hn
  exact hn
end RelativeAffineTestRule318
