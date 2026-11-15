module
public import VaryingWordTripleMaps318
public section
noncomputable section
namespace VaryingWordTripleCocycle318
open VaryingWordTripleMaps318 VaryingWordTripleAlgebra318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "K" x y z => VaryingWordTripleAlgebra318.ring R A ι x y z
local notation "N" x => VaryingNormalizedWordParameter318.ring R A ι x

/-- The actual coordinate-ring maps satisfy the period-three cocycle. -/
lemma cycle : ((rotateMap R A ι w v u).comp (rotateMap R A ι v u w)).comp
    (rotateMap R A ι u w v)=AlgHom.id R (K w v u) := by
  apply (points R A ι w v u (K w v u)).injective
  simp only [rotate_evaluate,rotate_universal,VaryingWordTriplePoints318.rotate_cycle]

lemma leg : (rotateMap R A ι w v u).comp (secondMap R A ι v u w)=
    (firstMap R A ι w v u).comp (VaryingNormalizedOverlapScheme318.transitionRing R A ι w v) := by
  apply (VaryingNormalizedWordOverlap318.pointsOnOpen R A ι v (K w v u) w).injective
  simp only [second_evaluate,rotate_universal,VaryingWordTriplePoints318.rotate_leg,
    VaryingWordOverlapIso318.transitionRing_evaluate]

/-- Both literal triple legs restrict to the same normalized w-chart. -/
lemma square : (secondMap R A ι w v u).comp
    (VaryingNormalizedWordOverlap318.inclusion R A ι w u)=
      (firstMap R A ι w v u).comp (VaryingNormalizedWordOverlap318.inclusion R A ι w v) := by
  apply (VaryingNormalizedWordParameter318.points R A ι w (K w v u)).injective
  exact congrArg (fun d : VaryingNormalizedWordOverlap318.Point R A ι w (K w v u) u => d.val)
    (second_universal R A ι w v u)

lemma second_base (z : N w) :
    secondMap R A ι w v u (algebraMap (N w)
      (VaryingNormalizedWordOverlap318.ring R A ι w u) z)=
      algebraMap (VaryingNormalizedWordOverlap318.ring R A ι w v) (K w v u)
        (algebraMap (N w) (VaryingNormalizedWordOverlap318.ring R A ι w v) z) :=
  congrArg (fun f : N w →ₐ[R] K w v u => f z) (square R A ι w v u)
end VaryingWordTripleCocycle318
