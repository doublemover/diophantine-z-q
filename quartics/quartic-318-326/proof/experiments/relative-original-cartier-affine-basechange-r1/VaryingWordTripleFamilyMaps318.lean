module
public import VaryingWordTripleFamily318
public section
noncomputable section
namespace VaryingWordTripleFamilyMaps318
open AlgebraicGeometry CategoryTheory
open VaryingWordTripleFamily318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "K" x y z => VaryingWordTripleAlgebra318.ring R A ι x y z
local notation "H" x y => VaryingNormalizedWordOverlap318.ring R A ι x y
local notation "Q" x y z => VaryingWordTripleFamily318.ring R A ι x y z
local notation "O" x y => VaryingWordOverlapFamily318.ring R A ι x y
@[expose] def firstMap : CommRingCat.of (O w v) ⟶ CommRingCat.of (Q w v u) :=
  AffineQuotientPushout318.arrow
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A (H w v) (K w v u)
      (VaryingWordTripleMaps318.firstMap R A ι w v u)).toRingHom)
    (VaryingWordOverlapFamily318.ideal R A ι w v) (ideal R A ι w v u) (first_ideal R A ι w v u)
@[expose] def secondMap : CommRingCat.of (O w u) ⟶ CommRingCat.of (Q w v u) :=
  AffineQuotientPushout318.arrow
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A (H w u) (K w v u)
      (VaryingWordTripleMaps318.secondMap R A ι w v u)).toRingHom)
    (VaryingWordOverlapFamily318.ideal R A ι w u) (ideal R A ι w v u) (second_ideal R A ι w v u)
@[expose] def rotateMap : CommRingCat.of (Q v u w) ⟶ CommRingCat.of (Q w v u) :=
  AffineQuotientPushout318.arrow
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A (K v u w) (K w v u)
      (VaryingWordTripleMaps318.rotateMap R A ι w v u)).toRingHom)
    (ideal R A ι v u w) (ideal R A ι w v u) (rotation_ideal R A ι w v u)

lemma first_mk (z : H w v ⊗[R] A) : (firstMap R A ι w v u).hom (Ideal.Quotient.mk _ z)=
    Ideal.Quotient.mk _ (Algebra.TensorProduct.map (VaryingWordTripleMaps318.firstMap R A ι w v u)
      (AlgHom.id R A) z) := rfl
lemma second_mk (z : H w u ⊗[R] A) : (secondMap R A ι w v u).hom (Ideal.Quotient.mk _ z)=
    Ideal.Quotient.mk _ (Algebra.TensorProduct.map (VaryingWordTripleMaps318.secondMap R A ι w v u)
      (AlgHom.id R A) z) := rfl
lemma rotate_mk (z : K v u w ⊗[R] A) : (rotateMap R A ι w v u).hom (Ideal.Quotient.mk _ z)=
    Ideal.Quotient.mk _ (Algebra.TensorProduct.map (VaryingWordTripleMaps318.rotateMap R A ι w v u)
      (AlgHom.id R A) z) := rfl
abbrev scheme : Scheme := Spec (CommRingCat.of (Q w v u))
@[expose] def first : scheme R A ι w v u ⟶ VaryingWordOverlapFamily318.scheme R A ι w v :=
  Spec.map (firstMap R A ι w v u)
@[expose] def second : scheme R A ι w v u ⟶ VaryingWordOverlapFamily318.scheme R A ι w u :=
  Spec.map (secondMap R A ι w v u)
@[expose] def rotation : scheme R A ι w v u ⟶ scheme R A ι v u w :=
  Spec.map (rotateMap R A ι w v u)
end VaryingWordTripleFamilyMaps318
