module
public import VaryingSourceActionClassifier318
public section
noncomputable section
namespace VaryingSourcePointNaturality318
open VaryingCommutingMatrixPoints318 VaryingSourceActionEquations318
open VaryingSourceActionParameter318
universe u
variable (R A ι S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
@[expose] def mapPoint (f : S →ₐ[R] T) (d : Point R A ι S) : Point R A ι T :=
  ⟨mapData R A ι S T f d.val,valid_map R A ι S T f d.val d.property⟩
lemma toPoint_natural (f : S →ₐ[R] T) (a : ring R A ι →ₐ[R] S) :
    toPoint R A ι T (f.comp a)=mapPoint R A ι S T f (toPoint R A ι S a) := by
  apply Subtype.ext
  exact forward_natural R A ι S T f (a.comp (quotient R A ι))
end VaryingSourcePointNaturality318
