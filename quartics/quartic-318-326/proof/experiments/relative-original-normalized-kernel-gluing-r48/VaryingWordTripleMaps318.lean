module
public import VaryingWordTripleAlgebra318
public section
noncomputable section
namespace VaryingWordTripleMaps318
open VaryingWordTripleAlgebra318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "K" x y z => VaryingWordTripleAlgebra318.ring R A ι x y z
local notation "H" x y => VaryingNormalizedWordOverlap318.ring R A ι x y
@[expose] def universal : VaryingWordTriplePoints318.Point R A ι w v u (K w v u) :=
  points R A ι w v u (K w v u) (AlgHom.id R (K w v u))
abbrev firstMap : H w v →ₐ[R] K w v u := inclusion R A ι w v u
@[expose] def secondMap : H w u →ₐ[R] K w v u :=
  (VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w (K w v u) u).symm
    (VaryingWordTriplePoints318.second R A ι w v u (K w v u) (universal R A ι w v u))
@[expose] def rotateMap : K v u w →ₐ[R] K w v u :=
  (points R A ι v u w (K w v u)).symm
    (VaryingWordTriplePoints318.rotate R A ι w v u (K w v u) (universal R A ι w v u))
lemma rotate_universal : points R A ι v u w (K w v u) (rotateMap R A ι w v u)=
    VaryingWordTriplePoints318.rotate R A ι w v u (K w v u) (universal R A ι w v u) :=
  (points R A ι v u w (K w v u)).apply_symm_apply _
lemma second_universal :
    VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w (K w v u) u (secondMap R A ι w v u)=
      VaryingWordTriplePoints318.second R A ι w v u (K w v u) (universal R A ι w v u) :=
  (VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w (K w v u) u).apply_symm_apply _

variable (S : Type u) [CommRing S] [Algebra R S]
lemma rotate_evaluate (a : K w v u →ₐ[R] S) :
    points R A ι v u w S (a.comp (rotateMap R A ι w v u))=
      VaryingWordTriplePoints318.rotate R A ι w v u S (points R A ι w v u S a) := by
  rw [show points R A ι v u w S (a.comp (rotateMap R A ι w v u))=
    VaryingWordTriplePoints318.mapPoint R A ι v u w (K w v u) S a
      (points R A ι v u w (K w v u) (rotateMap R A ι w v u)) from
    toPoint_natural R A ι v u w (K w v u) S a _]
  rw [rotate_universal,VaryingWordTriplePoints318.rotate_natural]
  have h := toPoint_natural R A ι w v u (K w v u) S a (AlgHom.id R (K w v u))
  simp only [AlgHom.comp_id] at h
  exact congrArg (VaryingWordTriplePoints318.rotate R A ι w v u S) h.symm

lemma second_evaluate (a : K w v u →ₐ[R] S) :
    VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w S u
      (a.comp (secondMap R A ι w v u))=
      VaryingWordTriplePoints318.second R A ι w v u S (points R A ι w v u S a) := by
  rw [show VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w S u
      (a.comp (secondMap R A ι w v u))=
      VaryingNormalizedWordOverlap318.mapPoint R A ι w (K w v u) u S a
        (VaryingNormalizedWordOverlap318.pointsOnOpen R A ι w (K w v u) u
          (secondMap R A ι w v u)) from
    VaryingNormalizedWordOverlap318.toPoint_natural R A ι w (K w v u) u S a _]
  rw [second_universal]
  have h := toPoint_natural R A ι w v u (K w v u) S a (AlgHom.id R (K w v u))
  simp only [AlgHom.comp_id] at h
  exact congrArg (VaryingWordTriplePoints318.second R A ι w v u S) h.symm

end VaryingWordTripleMaps318
