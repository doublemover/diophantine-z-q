module
public import VaryingNormalizedWordParameter318
public section
noncomputable section
namespace VaryingNormalizedWordNaturality318
open VaryingNormalizedWordParameter318 VaryingSourcePointNaturality318 VaryingMatrixWords318
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
variable (S T : Type u) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
variable (f : S →ₐ[R] T)
@[expose] def mapPoint (d : Point R A ι w S) : Point R A ι w T :=
  ⟨VaryingSourcePointNaturality318.mapPoint R A ι S T f d.val,by
    ext i j
    have h := congrArg f (congrFun (congrFun d.property i) j)
    change f (wordVector d.val.val (w j) i)=f ((1 : Matrix ι ι S) i j) at h
    rw [wordVector_map] at h
    change wordVector
      (VaryingCommutingMatrixPoints318.mapData R A ι S T f d.val.val) (w j) i=
      (1 : Matrix ι ι T) i j
    rw [h]
    simp only [Matrix.one_apply]
    split_ifs <;> simp⟩

lemma toPoint_natural (a : ring R A ι w →ₐ[R] S) :
    toPoint R A ι w T (f.comp a)=mapPoint R A ι w S T f (toPoint R A ι w S a) := by
  apply Subtype.ext
  exact VaryingSourcePointNaturality318.toPoint_natural R A ι S T f
    (a.comp (quotient R A ι w))

lemma determinant_map (d : Point R A ι w S) (v : ι → List A) :
    f (determinant d.val.val v)=determinant (mapPoint R A ι w S T f d).val.val v :=
  VaryingMatrixWords318.determinant_map R f d.val.val v
end VaryingNormalizedWordNaturality318
