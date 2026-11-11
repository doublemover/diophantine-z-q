module
public import VaryingNormalizedOverlapScheme318
public import CyclicNormalizationMatrixFormula318
public section
noncomputable section
open scoped Matrix
namespace VaryingWordTransitionNaturality318
open VaryingNormalizedWordOverlap318 VaryingNormalizedOverlapFrames318
open VaryingSourceFreeQuotientClassifier318 VaryingNormalizedWordFrame318
open CyclicNormalizationMatrixFormula318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S : Type u) [CommRing S] [Algebra R S] (v : ι → List A)
local notation "B" => (S ⊗[R] A)
local notation "words" t => (fun j => (1 : S) ⊗ₜ[R] (t j).prod)

lemma transition_matrix (d : Point R A ι w S v) (a : A) :
    (transition R A ι w S v d).val.val.val.matrices a=
      (VaryingMatrixWords318.columns d.val.val.val v)⁻¹ *
        d.val.val.val.matrices a * VaryingMatrixWords318.columns d.val.val.val v := by
  have h := action_matrix S B ι (framed R A ι w S d.val) (words v)
    (toFrames R A ι w S v d).property ((1 : S) ⊗ₜ[R] a)
  change (transition R A ι w S v d).val.val.val.matrices a=
    (CyclicWordNormalization318.columns S B ι
      (framed R A ι w S d.val) (words v))⁻¹ *
      (fromFramedData R A ι S (framed R A ι w S d.val)).map a *
      CyclicWordNormalization318.columns S B ι (framed R A ι w S d.val) (words v) at h
  have hw : CyclicWordNormalization318.columns S B ι
      (framed R A ι w S d.val) (words v)=VaryingMatrixWords318.columns d.val.val.val v :=
    frame_columns R A ι w S v d.val
  have hd : fromFramedData R A ι S (framed R A ι w S d.val)=
      sourceAction R A ι w S d.val := from_to_data R A ι S (cyclic R A ι w S d.val)
  rw [hw,hd] at h
  exact h

lemma transition_marked (d : Point R A ι w S v) :
    (transition R A ι w S v d).val.val.val.marked=
      (VaryingMatrixWords318.columns d.val.val.val v)⁻¹ *ᵥ d.val.val.val.marked := by
  change (CyclicWordNormalization318.columns S B ι
    (framed R A ι w S d.val) (words v))⁻¹ *ᵥ d.val.val.val.marked=_
  rw [frame_columns]

variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
lemma columns_map (d : Point R A ι w S v) :
    f.toRingHom.mapMatrix (VaryingMatrixWords318.columns d.val.val.val v)=
      VaryingMatrixWords318.columns (mapPoint R A ι w S v T f d).val.val.val v := by
  ext i j
  exact VaryingMatrixWords318.wordVector_map R f d.val.val.val (v j) i

/-- The actual normalization transition is coefficient-natural, not merely
an objectwise equivalence on algebraically closed field points. -/
lemma transition_natural (d : Point R A ι w S v) :
    mapPoint R A ι v S w T f (transition R A ι w S v d)=
      transition R A ι w T v (mapPoint R A ι w S v T f d) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply VaryingCommutingMatrixRing318.Data.ext
  · funext a
    change f.toRingHom.mapMatrix ((transition R A ι w S v d).val.val.val.matrices a)=_
    simp only [transition_matrix,map_mul,inverse_map ι f.toRingHom _ d.property,columns_map]
  · funext i
    change f ((transition R A ι w S v d).val.val.val.marked i)=_
    simp only [transition_marked,mulVec_map ι f.toRingHom,
      inverse_map ι f.toRingHom _ d.property,columns_map]
end VaryingWordTransitionNaturality318
