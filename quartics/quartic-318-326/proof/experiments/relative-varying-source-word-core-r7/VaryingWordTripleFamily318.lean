module
public import VaryingWordFamilyTransition318
public section
noncomputable section
namespace VaryingWordTripleFamily318
open VaryingWordTripleMaps318 VaryingNormalizedWordFrame318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "K" x y z => VaryingWordTripleAlgebra318.ring R A ι x y z
local notation "H" x y => VaryingNormalizedWordOverlap318.ring R A ι x y
@[expose] def data : VaryingNormalizedWordParameter318.Point R A ι w (K w v u) :=
  (universal R A ι w v u).val.val
@[expose] def frame := framed R A ι w (K w v u) (data R A ι w v u)
abbrev ideal := CyclicQuotientEvaluation318.ideal (frame R A ι w v u).action (frame R A ι w v u).marked
abbrev ring := (K w v u ⊗[R] A) ⧸ ideal R A ι w v u

lemma first_data : VaryingNormalizedWordNaturality318.mapPoint R A ι w (H w v) (K w v u)
    (firstMap R A ι w v u) (VaryingWordOverlapFamily318.data R A ι w v)=data R A ι w v u := by
  rw [VaryingWordOverlapFamily318.data_point]
  have h := VaryingNormalizedWordOverlap318.toPoint_natural R A ι w (H w v) v (K w v u)
    (firstMap R A ι w v u) (AlgHom.id R (H w v))
  simp only [AlgHom.comp_id] at h
  exact congrArg Subtype.val h.symm
lemma second_data : VaryingNormalizedWordNaturality318.mapPoint R A ι w (H w u) (K w v u)
    (secondMap R A ι w v u) (VaryingWordOverlapFamily318.data R A ι w u)=data R A ι w v u := by
  rw [VaryingWordOverlapFamily318.data_point]
  have h := VaryingNormalizedWordOverlap318.toPoint_natural R A ι w (H w u) u (K w v u)
    (secondMap R A ι w v u) (AlgHom.id R (H w u))
  simp only [AlgHom.comp_id] at h
  exact congrArg Subtype.val (h.symm.trans (second_universal R A ι w v u))
lemma rotation_data : VaryingNormalizedWordNaturality318.mapPoint R A ι v (K v u w) (K w v u)
    (rotateMap R A ι w v u) (data R A ι v u w)=
      (VaryingWordTriplePoints318.rotate R A ι w v u (K w v u) (universal R A ι w v u)).val.val := by
  have h := VaryingWordTripleAlgebra318.toPoint_natural R A ι v u w (K v u w) (K w v u)
    (rotateMap R A ι w v u) (AlgHom.id R (K v u w))
  simp only [AlgHom.comp_id] at h
  exact congrArg (fun d : VaryingWordTriplePoints318.Point R A ι v u w (K w v u) => d.val.val)
    (h.symm.trans (rotate_universal R A ι w v u))

lemma first_ideal : Ideal.map
    (VaryingNormalizedIdealBaseChange318.sourceMap R A (H w v) (K w v u) (firstMap R A ι w v u)).toRingHom
    (VaryingWordOverlapFamily318.ideal R A ι w v)=ideal R A ι w v u := by
  have h := VaryingNormalizedIdealBaseChange318.ideal_map R A ι w (H w v) (K w v u)
    (firstMap R A ι w v u) (VaryingWordOverlapFamily318.data R A ι w v)
  rw [first_data] at h
  exact h
lemma second_ideal : Ideal.map
    (VaryingNormalizedIdealBaseChange318.sourceMap R A (H w u) (K w v u) (secondMap R A ι w v u)).toRingHom
    (VaryingWordOverlapFamily318.ideal R A ι w u)=ideal R A ι w v u := by
  have h := VaryingNormalizedIdealBaseChange318.ideal_map R A ι w (H w u) (K w v u)
    (secondMap R A ι w v u) (VaryingWordOverlapFamily318.data R A ι w u)
  rw [second_data] at h
  exact h
lemma rotation_ideal : Ideal.map
    (VaryingNormalizedIdealBaseChange318.sourceMap R A (K v u w) (K w v u) (rotateMap R A ι w v u)).toRingHom
    (ideal R A ι v u w)=ideal R A ι w v u := by
  have h := VaryingNormalizedIdealBaseChange318.ideal_map R A ι v (K v u w) (K w v u)
    (rotateMap R A ι w v u) (data R A ι v u w)
  rw [rotation_data] at h
  exact h.trans (congrArg Subtype.val
    (VaryingWordTriplePoints318.rotate_ideal R A ι w v u (K w v u) (universal R A ι w v u)))
end VaryingWordTripleFamily318
