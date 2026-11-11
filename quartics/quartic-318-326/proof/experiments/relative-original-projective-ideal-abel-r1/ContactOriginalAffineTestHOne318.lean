module
public import ContactOriginalAffineTestCover318
public import NonreducedLineMayerVietoris318
public section
noncomputable section
namespace ContactOriginalAffineTestHOne318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalAffineTestCover318
variable (c : Fin 4 → ℚˣ) {T : Scheme.{0}} [IsAffine T]
  (b : T ⟶ Spec (CommRingCat.of ℚ)) (L : Line (family c b))

/-- On every original affine test, the SAME original derived H1 of ANY
actual line is the quotient of its genuine full-overlap sections by the
literal original finite/infinity restriction difference. This uses the
proved nonreduced acyclicity, not an assumed affine cohomology comparison. -/
def equivalence :
    Γ(L.object,finiteTest c b ⊓ infinityTest c b) ⧸
      (NonreducedLineMayerVietoris318.difference L (finiteTest c b) (infinityTest c b)).range ≃+
    NonreducedLineMayerVietoris318.H1 L :=
  NonreducedLineMayerVietoris318.equivalence L (finiteTest c b) (infinityTest c b)
    (finiteTest_affine c b) (infinityTest_affine c b) (test_cover c b)

/-- Every actual derived class is represented by an ORIGINAL overlap
section on this SAME test curve, with no field/reducedness restriction. -/
theorem boundary_surjective : Function.Surjective
    (NonreducedLineMayerVietoris318.boundary L (finiteTest c b) (infinityTest c b) (test_cover c b)) :=
  NonreducedLineMayerVietoris318.boundary_surjective L (finiteTest c b) (infinityTest c b)
    (finiteTest_affine c b) (infinityTest_affine c b) (test_cover c b)

lemma equivalence_mk (x : Γ(L.object,finiteTest c b ⊓ infinityTest c b)) :
    equivalence c b L (QuotientAddGroup.mk x) =
      NonreducedLineMayerVietoris318.boundary L (finiteTest c b) (infinityTest c b)
        (test_cover c b) x := rfl
end ContactOriginalAffineTestHOne318
