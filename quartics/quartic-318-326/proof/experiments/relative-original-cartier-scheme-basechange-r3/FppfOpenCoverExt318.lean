module
public import RelativeFppfLineSheaf318
public import Mathlib.CategoryTheory.Sites.Sheaf
public section
noncomputable section
namespace FppfOpenCoverExt318
open AlgebraicGeometry CategoryTheory Opposite
variable {S B : Scheme.{0}} (b : B ⟶ S) (U : B.OpenCover)
@[expose] def object (i : U.I₀) : Over S := Over.mk (U.f i ≫ b)
@[expose] def arrow (i : U.I₀) : object b U i ⟶ Over.mk b := Over.homMk (U.f i) rfl

/-- The ACTUAL scheme open cover is a covering sieve in the existing
big relative fppf topology, with its original maps in Over S. -/
lemma covering : Sieve.ofArrows (object b U) (arrow b U) ∈
    RelativeFppfLineSheaf318.topology S (Over.mk b) := by
  rw [RelativeFppfLineSheaf318.topology,GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  apply (Scheme.ofArrows_mem_precoverage_iff (P:=@Flat ⊓ @LocallyOfFinitePresentation)).mpr
  constructor
  · intro x
    obtain ⟨y,hy⟩ := U.covers x
    exact ⟨U.idx x,y,hy⟩
  · intro i
    exact ⟨inferInstance,inferInstance⟩

/-- Equality of elements of an actual fppf group sheaf can be checked on
this full original coefficient cover. No arbitrary local-equivalence
relation is substituted for the associated sheaf. -/
lemma elements_ext (F : Sheaf (RelativeFppfLineSheaf318.topology S) CommGrpCat.{1})
    (x y : F.obj.obj (op (Over.mk b)))
    (h : ∀ i,F.obj.map (arrow b U i).op x=F.obj.map (arrow b U i).op y) : x=y := by
  have hf : Presheaf.IsSheaf (RelativeFppfLineSheaf318.topology S)
      (F.obj ⋙ forget CommGrpCat.{1}) :=
    (Presheaf.isSheaf_iff_isSheaf_forget (forget CommGrpCat.{1})).mp F.property
  have ht := (isSheaf_iff_isSheaf_of_type (F.obj ⋙ forget CommGrpCat.{1})).mp hf
  apply (ht.isSheafFor (Presieve.ofArrows (object b U) (arrow b U))
    (covering b U)).isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  exact h i
end FppfOpenCoverExt318
