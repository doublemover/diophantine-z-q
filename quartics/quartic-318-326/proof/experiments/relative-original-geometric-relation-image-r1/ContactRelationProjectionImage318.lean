module
public import ContactAffinePicardRelationWitness318
public import MorphismImageSieve318
public section
noncomputable section
namespace ContactRelationProjectionImage318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "B" => Over.mk (baseMap R)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- The existing difference-frame parameter as an actual object of the
SAME big relative site. No new quotient or replacement scheme is introduced. -/
@[expose] def object : Over Q := Over.mk
  (ContactGeometricIsomRelationWitness318.projection R c L K ≫ baseMap R)
@[expose] def projection : object R c L K ⟶ B :=
  Over.homMk (ContactGeometricIsomRelationWitness318.projection R c L K) rfl
/-- Exact whole-site factorization witnesses coincide with the old
whole-scheme points over the literal coefficient arrow. -/
lemma membership (T : Over Q) (f : T ⟶ B) :
    MorphismImageSieve318.image (projection R c L K) f ↔
    Nonempty {z : T.left ⟶ ContactGeometricIsomRelationWitness318.parameter R c L K //
      z ≫ ContactGeometricIsomRelationWitness318.projection R c L K=f.left} := by
  constructor
  · rintro ⟨z,hz⟩
    exact ⟨⟨z.left,congrArg (fun e => e.left) hz⟩⟩
  · rintro ⟨⟨z,hz⟩⟩
    refine ⟨Over.homMk z ?_,?_⟩
    · change z ≫ (ContactGeometricIsomRelationWitness318.projection R c L K ≫ baseMap R)=T.hom
      rw [←Category.assoc,hz,f.w]
    · apply Over.OverMorphism.ext
      exact hz
/-- The entire original absolute equality sieve IS the image sieve of
this concrete projection. This is stronger than a field-point relation,
but is not representability of the full Isom functor or of the quotient. -/
lemma equalizer_eq_image :
    Presheaf.equalizerSieve
      (show (OriginalAbsoluteLinePresheaf318.presheaf p).obj (op B) from classOf L)
      (show (OriginalAbsoluteLinePresheaf318.presheaf p).obj (op B) from classOf K)=
      MorphismImageSieve318.image (projection R c L K) := by
  ext T f
  exact (ContactAffinePicardRelationWitness318.membership R c L K T f).trans
    (membership R c L K T f).symm
end ContactRelationProjectionImage318
