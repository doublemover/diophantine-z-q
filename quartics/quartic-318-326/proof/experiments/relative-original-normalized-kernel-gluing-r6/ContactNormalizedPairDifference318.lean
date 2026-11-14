module
public import ContactNormalizedPairClass318
public section
noncomputable section
namespace ContactNormalizedPairDifference318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactNormalizedPairData318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (A B : Line (curve R c))
  (hA : ∀ x : NonreducedLineMayerVietoris318.H1 A,x=0)
  (hB : ∀ x : NonreducedLineMayerVietoris318.H1 B,x=0)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "t" => projection R c A B hA hB
local notation "N" => firstBound R c A hA
local notation "M" => secondBound R c B hB
/-- Both full-ideal effective families define a genuine point of the
previous all-bound difference presheaf on the actual common parameter. -/
@[expose] def datum : (ContactCartierDifferencePresheaf318.presheaf c).obj
    (Opposite.op (Over.mk (t ≫ baseMap R))) :=
  (⟨N,firstData R c A B hA hB⟩,⟨M,secondData R c A B hA hB⟩)
/-- The relative line already compared with the original class is the
pullback of the SAME actual O(D-E) line used by the absolute moduli Abel
map. Reassociation does not substitute a new line family. -/
lemma absolute_class : classOf (ContactNormalizedPairClass318.line R c A B hA hB)=
    classOf (LineSheafPullback318.line (RelativeAmbientReassociation318.comparison p (baseMap R) t).hom
      (ContactCartierDifferenceLine318.line c N M (t ≫ baseMap R)
        (firstData R c A B hA hB) (secondData R c A B hA hB))) := by
  change classOf (LineSheafTensor318.line
    (LineSheafPullback318.line (RelativeAmbientReassociation318.comparison p (baseMap R) t).hom _)
    (FramedLineInverse318.inverse (LineSheafPullback318.line
      (RelativeAmbientReassociation318.comparison p (baseMap R) t).hom _)))=
    LineClassPullbackHom318.pullback (RelativeAmbientReassociation318.comparison p (baseMap R) t).hom
      (classOf (LineSheafTensor318.line _ (FramedLineInverse318.inverse _)))
  rw [LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,
    LineSheafClassGroup318.classOf_tensor,LineSheafClassGroup318.classOf_inverse,map_mul,map_inv]
  rfl
@[expose] def absoluteIso : (ContactNormalizedPairClass318.line R c A B hA hB).object ≅
    (LineSheafPullback318.line (RelativeAmbientReassociation318.comparison p (baseMap R) t).hom
      (ContactCartierDifferenceLine318.line c N M (t ≫ baseMap R)
        (firstData R c A B hA hB) (secondData R c A B hA hB))).object :=
  Classical.choice ((classOf_eq_iff _ _).mp (absolute_class R c A B hA hB))
end ContactNormalizedPairDifference318
