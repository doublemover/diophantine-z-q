module
public import GradedAffineLine318
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public section
noncomputable section
namespace ProjectiveAffineLine318
open MvPolynomial Graded HomogeneousIdeal AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R]
abbrev grading := ProjectiveJLine318.grading R
abbrev gh (a:Rˣ) (b:R) := GradedAffineLine318.gradedHom R a b
lemma gh_X1 (a:Rˣ) (b:R) : gh R a b (X 1)=X 1 := GradedAffineLine318.hom_X1 R a b
lemma gh_C (a:Rˣ) (b r:R) : gh R a b (C r)=C r := GradedAffineLine318.hom_C R a b r
lemma gh_inverse (a:Rˣ) (b:R) : (gh R a b).comp (gh R a⁻¹ (-((a⁻¹:Rˣ):R)*b))=.id (grading R) := by
  apply GradedRingHom.ext
  intro p
  exact congrArg (fun f : GradedAffineLine318.Poly R →ₐ[R] GradedAffineLine318.Poly R => f p)
    (GradedAffineLine318.hom_inverse R a b)
lemma inverse_gh (a:Rˣ) (b:R) : (gh R a⁻¹ (-((a⁻¹:Rˣ):R)*b)).comp (gh R a b)=.id (grading R) := by
  apply GradedRingHom.ext
  intro p
  exact congrArg (fun f : GradedAffineLine318.Poly R →ₐ[R] GradedAffineLine318.Poly R => f p)
    (GradedAffineLine318.inverse_hom R a b)
lemma irrelevant_le (a:Rˣ) (b:R) : (grading R)₊ ≤ (grading R)₊.map (gh R a b) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi p hp
  have hmem : gh R a⁻¹ (-((a⁻¹:Rˣ):R)*b) p ∈ (grading R)₊ :=
    mem_irrelevant_of_mem _ hi (Graded.map_mem _ hp)
  have hm := Ideal.mem_map_of_mem (gh R a b).toRingHom hmem
  have he : gh R a b (gh R a⁻¹ (-((a⁻¹:Rˣ):R)*b) p)=p :=
    congrArg (fun f : grading R →+*ᵍ grading R => f p) (gh_inverse R a b)
  change gh R a b (gh R a⁻¹ (-((a⁻¹:Rˣ):R)*b) p) ∈ ((grading R)₊.map (gh R a b)).toIdeal at hm
  rw [he] at hm
  exact hm
@[expose] def map (a:Rˣ) (b:R) : ProjectiveJLine318.scheme R ⟶ ProjectiveJLine318.scheme R :=
  Proj.map (gh R a b) (irrelevant_le R a b)
lemma map_inverse (a:Rˣ) (b:R) : map R a b ≫ map R a⁻¹ (-((a⁻¹:Rˣ):R)*b)=𝟙 _ := by
  unfold map
  rw [← Proj.map_comp]
  simp only [gh_inverse, Proj.map_id]
lemma inverse_map (a:Rˣ) (b:R) : map R a⁻¹ (-((a⁻¹:Rˣ):R)*b) ≫ map R a b=𝟙 _ := by
  unfold map
  rw [← Proj.map_comp]
  simp only [inverse_gh, Proj.map_id]
@[expose] def iso (a:Rˣ) (b:R) : ProjectiveJLine318.scheme R ≅ ProjectiveJLine318.scheme R where
  hom := map R a b
  inv := map R a⁻¹ (-((a⁻¹:Rˣ):R)*b)
  hom_inv_id := map_inverse R a b
  inv_hom_id := inverse_map R a b
end ProjectiveAffineLine318
