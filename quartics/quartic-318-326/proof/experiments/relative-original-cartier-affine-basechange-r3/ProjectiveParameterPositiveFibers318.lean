module
public import ProjectiveParameterFieldPoint318
public import ProjectiveParameterSchemeSmooth318
public import Mathlib.AlgebraicGeometry.Fiber
public section
noncomputable section
namespace ProjectiveParameterPositiveFibers318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
variable (R : CommRingCat.{0}) (P : Type) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- The original coefficient action on the actual scheme residue field. -/
@[expose] def residueMap (x : Spec R) : R ⟶ (Spec R).residueField x :=
  Spec.preimage ((Spec R).fromSpecResidueField x)

/-- An explicit geometric positivity boundary: the actual section module
has a nonzero vector after EVERY original residue-field base change. -/
@[expose] def PositiveFibers : Prop := ∀ x : Spec R,
  letI : Algebra R ((Spec R).residueField x) := (residueMap R x).hom.toAlgebra
  ∃ v : (Spec R).residueField x ⊗[R] P,v≠0

/-- Positive actual residue fibers make the SAME glued parameter
surjective. Fieldwise normalization constructs each preimage. -/
theorem surjective (h : PositiveFibers R P) :
    Surjective (ProjectiveParameterSliceBase318.projection R P) := by
  constructor
  intro x
  let K := (Spec R).residueField x
  letI : Algebra R K := (residueMap R x).hom.toAlgebra
  obtain ⟨v,hv⟩ := h x
  obtain ⟨i,g,hg⟩ := ProjectiveParameterFieldPoint318.exists_chart_map R P K v hv
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R K))=
      (Spec R).fromSpecResidueField x := by
    change Spec.map (residueMap R x)=_
    exact Spec.map_preimage _
  let t : Spec K := IsLocalRing.closedPoint K
  refine ⟨ProjectiveParameterSliceGluing318.into R P i (g t),?_⟩
  have hm := congrArg (fun f : Spec K ⟶ Spec R => f t)
    ((congrArg (fun f => g ≫ f) (ProjectiveParameterSliceBase318.into_projection R P i)).trans hg)
  simpa only [Scheme.Hom.comp_apply,hb,Scheme.fromSpecResidueField_apply] using hm

/-- Smooth, surjective and locally finitely presented over the original
base under the precise residue-positivity input; no represented Picard
object or surjectivity of the Abel transformation is assumed. -/
theorem smooth_surjective (h : PositiveFibers R P) :
    Smooth (ProjectiveParameterSliceBase318.projection R P) ∧
    Surjective (ProjectiveParameterSliceBase318.projection R P) ∧
    LocallyOfFinitePresentation (ProjectiveParameterSliceBase318.projection R P) :=
  ⟨inferInstance,surjective R P h,inferInstance⟩
end ProjectiveParameterPositiveFibers318
