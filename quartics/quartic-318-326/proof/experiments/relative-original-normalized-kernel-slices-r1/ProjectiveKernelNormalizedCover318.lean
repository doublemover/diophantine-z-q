module
public import ProjectiveKernelNormalizedLaurent318
public import FppfSingleCover318
public section
noncomputable section
namespace ProjectiveKernelNormalizedCover318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "A" => ProjectiveSectionParameter318.algebra R P
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "H" => ProjectiveParameterPrincipalNormalization318.ring R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
variable (i : Fin F.size)
local notation "D" => ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d i
local notation "e" => ProjectiveKernelNormalizedLaurent318.schemeIso R P Q d i
local notation "q" => ProjectiveKernelNormalizedLaurent318.projection R P Q d i
@[expose] def section : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of D) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id C) (1:Cˣ))) ≫ e.inv
/-- The Laurent coordinate-one section splits the ACTUAL normalized
kernel chart map, including over arbitrary nilpotent coefficient rings. -/
@[reassoc] lemma section_projection : section R P Q d i ≫ q=𝟙 _ := by
  have hc : CommRingCat.ofHom (algebraMap C (LaurentPolynomial C)) ≫
      CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id C) (1:Cˣ))=𝟙 (CommRingCat.of C) := by
    apply CommRingCat.hom_ext
    ext x
    exact LaurentPolynomial.eval₂_C _ _ x
  simp only [section,ProjectiveKernelNormalizedLaurent318.projection,Category.assoc,Iso.inv_hom_id_assoc]
  rw [←Spec.map_comp,hc,Spec.map_id]
instance surjective : Surjective q := by
  constructor
  intro x
  refine ⟨section R P Q d i x,?_⟩
  have h := congrArg (fun f => f x) (section_projection R P Q d i)
  change q (section R P Q d i x)=x at h
  exact h
/-- A real smooth affine fppf chart quotient onto its represented
normalized slice. This does not assert the global projective quotient. -/
lemma covering : Sieve.ofArrows (fun _ : PUnit => Over.mk q)
    (fun _ => Over.homMk q (Category.comp_id q)) ∈
      RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of C)) (Over.mk (𝟙 _)) :=
  FppfSingleCover318.covering (𝟙 _) q q (Category.comp_id q)

end ProjectiveKernelNormalizedCover318
