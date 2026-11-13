module
public import VaryingSourceCoefficientPullback318
public import AffineQuotientPushout318
public section
noncomputable section
namespace VaryingWholeIdealFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A S : Type u) [CommRing R] [CommRing A] [Algebra R A] [CommRing S] [Algebra R S]
variable (I : Ideal (S ⊗[R] A))
abbrev family : Scheme := Spec (CommRingCat.of ((S ⊗[R] A) ⧸ I))
abbrev into : family R A S I ⟶ Spec (CommRingCat.of (S ⊗[R] A)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
instance closed : IsClosedImmersion (into R A S I) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
abbrev projection : family R A S I ⟶ Spec (CommRingCat.of S) :=
  into R A S I ≫ VaryingSourceCoefficientPullback318.projection R A S
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
@[expose] def extended : Ideal (T ⊗[R] A) :=
  Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom I
@[expose] def map : family R A T (extended R A S I T f) ⟶ family R A S I :=
  Spec.map (AffineQuotientPushout318.arrow
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom) I _ rfl)
lemma source_cartesian : IsPullback (into R A T (extended R A S I T f)) (map R A S I T f)
    (VaryingSourceCoefficientPullback318.sourceChange R A S T f) (into R A S I) :=
  AffineQuotientPushout318.pullback
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom) I _ rfl
@[reassoc] lemma map_into : map R A S I T f ≫ into R A S I=
    into R A T (extended R A S I T f) ≫ VaryingSourceCoefficientPullback318.sourceChange R A S T f :=
  (source_cartesian R A S I T f).w.symm
/-- Arbitrary full quotient ideals, without cyclic/free assumptions,
commute with actual coefficient base change as entire scheme families. -/
lemma cartesian : IsPullback (map R A S I T f) (projection R A T (extended R A S I T f))
    (projection R A S I) (VaryingSourceCoefficientPullback318.coefficientChange R S T f) :=
  (source_cartesian R A S I T f).flip.paste_vert
    (VaryingSourceCoefficientPullback318.cartesian R A S T f)
end VaryingWholeIdealFamily318
