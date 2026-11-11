module
public import VaryingQuotientCoefficientPullback318
public section
noncomputable section
namespace VaryingWordOverlapFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingNormalizedWordOverlap318 VaryingNormalizedWordFrame318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v : ι → List A)
local notation "N" t => VaryingNormalizedWordParameter318.ring R A ι t
local notation "H" s t => VaryingNormalizedWordOverlap318.ring R A ι s t
@[expose] def point : Point R A ι w (H w v) v :=
  pointsOnOpen R A ι w (H w v) v (AlgHom.id R (H w v))
@[expose] def data : VaryingNormalizedWordParameter318.Point R A ι w (H w v) :=
  VaryingNormalizedWordNaturality318.mapPoint R A ι w (N w) (H w v)
    (inclusion R A ι w v) (universal R A ι w)
lemma data_point : data R A ι w v=(point R A ι w v).val := by
  have h := VaryingNormalizedWordNaturality318.toPoint_natural R A ι w (N w) (H w v)
    (inclusion R A ι w v) (AlgHom.id R (N w))
  simpa only [AlgHom.comp_id] using h.symm
@[expose] def frame := framed R A ι w (H w v) (data R A ι w v)
abbrev ideal := CyclicQuotientEvaluation318.ideal (frame R A ι w v).action (frame R A ι w v).marked
abbrev ring := (H w v ⊗[R] A) ⧸ ideal R A ι w v
abbrev scheme : Scheme := Spec (CommRingCat.of (ring R A ι w v))
abbrev projection : scheme R A ι w v ⟶ VaryingNormalizedOverlapScheme318.overlap R A ι w v :=
  CyclicQuotientFiniteFlat318.projection (frame R A ι w v).action (frame R A ι w v).marked
@[expose] def into : scheme R A ι w v ⟶ VaryingNormalizedUniversalFamily318.family R A ι w :=
  Spec.map (VaryingNormalizedFamilyBaseChange318.quotientMap R A ι w (N w) (H w v)
    (inclusion R A ι w v) (universal R A ι w))
lemma cartesian : IsPullback (into R A ι w v) (projection R A ι w v)
    (VaryingNormalizedUniversalFamily318.projection R A ι w)
    (VaryingNormalizedOverlapScheme318.into R A ι w v) :=
  VaryingQuotientCoefficientPullback318.cartesian R A ι w (N w) (universal R A ι w)
    (H w v) (inclusion R A ι w v)
instance into_open : IsOpenImmersion (into R A ι w v) :=
  MorphismProperty.of_isPullback (cartesian R A ι w v).flip inferInstance
@[expose] def comparison : scheme R A ι w v ≅
    pullback (VaryingNormalizedUniversalFamily318.projection R A ι w)
      (VaryingNormalizedOverlapScheme318.into R A ι w v) :=
  (cartesian R A ι w v).isoPullback
end VaryingWordOverlapFamily318
