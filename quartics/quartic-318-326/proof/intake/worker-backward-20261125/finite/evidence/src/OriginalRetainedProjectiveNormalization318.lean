module

public import OriginalRetainedComplexPointsOverEEquiv318
public import ProjectiveChart318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Analysis.Complex.Basic

@[expose] public section
noncomputable section

namespace OriginalRetainedProjectiveAffinePiece318

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev Grading := ProjectiveChart318.Grading ℂ ι
abbrev Ambient := AlgebraicGeometry.Proj (Grading ι)
abbrev Poly (i : ι) := MvPolynomial {j : ι // j≠i} ℂ
abbrev T := Spec (CommRingCat.of ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem variable_degree_one (i : ι) :
    (MvPolynomial.X i : MvPolynomial ι ℂ) ∈ Grading ι 1 :=
  MvPolynomial.isHomogeneous_X ℂ i

/-- The actual homogeneous projective structure map uses the original
degree-zero coefficients, not an abstract projective point set. -/
def projectiveBase : Ambient ι ⟶ T :=
  Proj.toSpecZero (Grading ι)≫Spec.map (CommRingCat.ofHom (ProjectiveChart318.coeffZero ℂ ι))

def affineArrow (i : ι) : Spec (CommRingCat.of (Poly ι i))⟶Ambient ι :=
  Spec.map (ProjectiveChart318.chartEquiv ℂ ι i).toRingEquiv.toCommRingCatIso.hom≫
    Proj.awayι (Grading ι) (MvPolynomial.X i) (variable_degree_one ι i) (by decide)

instance affineCoefficient_iso (i : ι) :
    IsIso (Spec.map (ProjectiveChart318.chartEquiv ℂ ι i).toRingEquiv.toCommRingCatIso.hom) := by
  let e := (ProjectiveChart318.chartEquiv ℂ ι i).toRingEquiv.toCommRingCatIso
  let : IsIso e.hom := inferInstance
  let : IsIso e.hom.op := inferInstance
  change IsIso (Scheme.Spec.map e.hom.op)
  infer_instance

instance affineArrow_open (i : ι) : IsOpenImmersion (affineArrow ι i) := by
  let f := Spec.map (ProjectiveChart318.chartEquiv ℂ ι i).toRingEquiv.toCommRingCatIso.hom
  let g := Proj.awayι (Grading ι) (MvPolynomial.X i) (variable_degree_one ι i) (by decide)
  let : IsIso f := affineCoefficient_iso ι i
  let : IsOpenImmersion f := IsOpenImmersion.of_isIso f
  let : IsOpenImmersion g := by
    let U := Proj.basicOpen (Grading ι) (MvPolynomial.X i)
    let C := Proj.basicOpenIsoSpec (Grading ι) (MvPolynomial.X i)
      (variable_degree_one ι i) (by decide)
    let : IsIso C.inv := inferInstance
    let : IsOpenImmersion C.inv := IsOpenImmersion.of_isIso C.inv
    let : IsOpenImmersion U.ι := by
      change IsOpenImmersion ((Ambient ι).ofRestrict U.isOpenEmbedding)
      exact IsOpenImmersion.ofRestrict (Ambient ι) U.isOpenEmbedding
    change IsOpenImmersion (C.inv≫U.ι)
    exact IsOpenImmersion.comp C.inv U.ι
  change IsOpenImmersion (f≫g)
  exact IsOpenImmersion.comp f g

theorem affineArrow_base (i : ι) :
    affineArrow ι i≫projectiveBase ι =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Poly ι i))) := by
  unfold affineArrow projectiveBase
  have baseEq := Proj.awayι_toSpecZero (Grading ι) (MvPolynomial.X i)
    (variable_degree_one ι i) (by decide)
  rw [Category.assoc,←Category.assoc
    (Proj.awayι (Grading ι) (MvPolynomial.X i) (variable_degree_one ι i) (by decide)),
    baseEq,←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (ProjectiveChart318.chartEquiv ℂ ι i).toRingHom.comp (ProjectiveChart318.coeff ℂ ι i) =
    algebraMap ℂ (Poly ι i)
  exact RingHom.ext (fun c => (ProjectiveChart318.chartEquiv ℂ ι i).commutes c)

theorem affineArrow_range (i : ι) :
    (affineArrow ι i).opensRange = Proj.basicOpen (Grading ι) (MvPolynomial.X i) := by
  unfold affineArrow
  rw [Scheme.Hom.opensRange_comp_of_isIso,Proj.opensRange_awayι]

omit [Fintype ι] [DecidableEq ι] in
theorem variables_generate :
    Algebra.adjoin (Grading ι 0) (Set.range (MvPolynomial.X : ι→MvPolynomial ι ℂ)) = ⊤ := by
  let S := Algebra.adjoin (Grading ι 0) (Set.range (MvPolynomial.X : ι→MvPolynomial ι ℂ))
  suffices ∀ p, p∈S from top_unique (fun p _ => this p)
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => exact S.algebraMap_mem (ProjectiveChart318.coeffZero ℂ ι r)
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p j hp => exact S.mul_mem hp (Algebra.subset_adjoin ⟨j,rfl⟩)

omit [Fintype ι] [DecidableEq ι] in
theorem ambient_affines_cover :
    (⨆ i : ι, Proj.basicOpen (Grading ι) (MvPolynomial.X i))=⊤ :=
  Proj.iSup_basicOpen_eq_top' (Grading ι) MvPolynomial.X
    (fun i => ⟨1,variable_degree_one ι i⟩) (variables_generate ι)


end OriginalRetainedProjectiveAffinePiece318
