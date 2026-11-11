module
public import CyclicWordFrameOverlap318
public section
noncomputable section
namespace CyclicWordFrameCocycle318
open FreeQuotientFramedClassifier318 CyclicWordNormalization318
open CyclicNormalizedFrameUniqueness318 CyclicWordFrameOverlap318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]
variable (d : Framed R A ι) (v u : ι → A)
  (hv : IsUnit (columns R A ι d v).det) (hu : IsUnit (columns R A ι d u).det)

/-- Change to the v-word frame, then to the u-word frame, equals the
direct change to u. The same full ideal controls both routes. -/
lemma normalization_cocycle :
    normalize R A ι (normalize R A ι d v hv) u
      (unit_after_normalize R A ι d v hv u hu)=normalize R A ι d u hu :=
  eq_of_ideal R A ι _ _ u
    (normalize_is_normalized R A ι _ u _)
    (normalize_is_normalized R A ι d u hu)
    (((normalize_ideal R A ι _ u _).trans (normalize_ideal R A ι d v hv)).trans
      (normalize_ideal R A ι d u hu).symm)

lemma normalization_identity (w : ι → A) (h : Normalized R A ι d w) :
    normalize R A ι d w (normalized_unit R A ι d w h)=d :=
  eq_of_ideal R A ι _ _ w (normalize_is_normalized R A ι d w _) h
    (normalize_ideal R A ι d w _)
end CyclicWordFrameCocycle318
