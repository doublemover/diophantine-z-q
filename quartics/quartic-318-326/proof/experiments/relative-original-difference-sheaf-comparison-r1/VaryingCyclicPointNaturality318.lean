module
public import VaryingCyclicDeterminantCover318
public section
noncomputable section
namespace VaryingCyclicPointNaturality318
open VaryingSourceFreeQuotientClassifier318 VaryingSourceTensorAction318
open VaryingCyclicNormalizedChart318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (w : ι → List A) (S : Type u) [CommRing S] [Algebra R S]
local notation "F" d => VaryingNormalizedWordFrame318.framed R A ι w S d
lemma point_eq_of_ideal (d e : VaryingNormalizedWordParameter318.Point R A ι w S)
    (h : ideal (F d).action (F d).marked=ideal (F e).action (F e).marked) : d=e := by
  apply (VaryingNormalizedFrameEquiv318.frames R A ι w S).injective
  apply Subtype.ext
  apply CyclicNormalizedFrameUniqueness318.eq_of_ideal S (S ⊗[R] A) ι (F d) (F e)
    (fun j => (1 : S) ⊗ₜ[R] (w j).prod)
    (VaryingNormalizedWordFrame318.normalized R A ι w S d)
    (VaryingNormalizedWordFrame318.normalized R A ι w S e)
  exact Subtype.ext h
variable (a : Cyclic R A ι S)
  (h : IsUnit (VaryingMatrixWords318.determinant
    (VaryingSourceActionClassifier318.point R A ι S a.data).val w))
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "aT" => VaryingCyclicCoefficientSections318.mapCyclic R A ι S a T f
lemma unit_map : IsUnit (VaryingMatrixWords318.determinant
    (VaryingSourceActionClassifier318.point R A ι T aT.data).val w) := by
  rw [← VaryingSourceSurjectiveCoefficient318.determinant_map R A ι S T f a.data w]
  exact h.map f.toMonoidHom
local notation "dS" => point R A ι S a w h
local notation "dT" => point R A ι T aT w (unit_map R A ι w S a h T f)
lemma point_natural : VaryingNormalizedWordNaturality318.mapPoint R A ι w S T f dS=dT := by
  apply point_eq_of_ideal R A ι w T
  calc
    _=Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom
        (ideal (VaryingNormalizedWordFrame318.framed R A ι w S dS).action
          (VaryingNormalizedWordFrame318.framed R A ι w S dS).marked) :=
      (VaryingNormalizedIdealBaseChange318.ideal_map R A ι w S T f dS).symm
    _=Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom
        (ideal (toFramed R A ι S a).action (toFramed R A ι S a).marked) :=
      congrArg (Ideal.map (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom)
        (ideal_point R A ι S a w h)
    _=ideal (toFramed R A ι T aT).action (toFramed R A ι T aT).marked :=
      VaryingCyclicIdealBaseChange318.ideal_map R A ι S a T f
    _=_ := (ideal_point R A ι T aT w (unit_map R A ι w S a h T f)).symm
lemma coordinate_natural : f.comp (coordinate R A ι S a w h)=
    coordinate R A ι T aT w (unit_map R A ι w S a h T f) := by
  apply (VaryingNormalizedWordParameter318.points R A ι w T).injective
  change VaryingNormalizedWordParameter318.toPoint R A ι w T _=
    VaryingNormalizedWordParameter318.toPoint R A ι w T _
  rw [VaryingNormalizedWordNaturality318.toPoint_natural,coordinate_point,coordinate_point]
  exact point_natural R A ι w S a h T f

open AlgebraicGeometry CategoryTheory
lemma schemeMap_natural : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ schemeMap R A ι S a w h=
    schemeMap R A ι T aT w (unit_map R A ι w S a h T f) := by
  rw [schemeMap,schemeMap,← Category.assoc,← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (f.comp (coordinate R A ι S a w h)).toRingHom) ≫ _=_
  rw [coordinate_natural]
end VaryingCyclicPointNaturality318
