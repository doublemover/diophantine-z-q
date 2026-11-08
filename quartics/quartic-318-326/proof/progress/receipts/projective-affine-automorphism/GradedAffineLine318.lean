module
public import JLineAtlas318
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public section
noncomputable section
namespace GradedAffineLine318
open MvPolynomial Graded HomogeneousIdeal
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R:Type*) [CommRing R]
abbrev Poly:=MvPolynomial (Fin 2) R
abbrev grading:=ProjectiveJLine318.grading R
@[expose] def variableImage (a:Rˣ) (b:R) (i:Fin 2):Poly R:=
  if i=0 then C (a:R)*X 0+C b*X 1 else X 1
@[expose] def hom (a:Rˣ) (b:R):Poly R→ₐ[R]Poly R:=aeval (variableImage R a b)
@[simp] theorem hom_X0 (a:Rˣ) (b:R):hom R a b (X 0)=C (a:R)*X 0+C b*X 1:=by simp [hom,variableImage]
@[simp] theorem hom_X1 (a:Rˣ) (b:R):hom R a b (X 1)=X 1:=by simp [hom,variableImage]
@[simp] theorem hom_C (a:Rˣ) (b r:R):hom R a b (C r)=C r:=by simp [hom]
lemma variableImage_homogeneous (a:Rˣ) (b:R) (i:Fin 2):
    (variableImage R a b i).IsHomogeneous 1:=by
  fin_cases i
  · exact (isHomogeneous_C_mul_X (a:R) 0).add (isHomogeneous_C_mul_X b 1)
  · exact isHomogeneous_X R 1
@[expose] def gradedHom (a:Rˣ) (b:R):grading R→+*ᵍ grading R where
  __ := (hom R a b).toRingHom
  map_mem {i} {p} hp := by
    change (hom R a b p).IsHomogeneous i
    simpa only [hom, one_mul] using (show p.IsHomogeneous i from hp).aeval
      (variableImage R a b) (variableImage_homogeneous R a b)
lemma hom_inverse (a:Rˣ) (b:R):
    (hom R a b).comp (hom R a⁻¹ (-((a⁻¹:Rˣ):R)*b))=AlgHom.id R (Poly R):=by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change hom R a b (hom R a⁻¹ (-((a⁻¹:Rˣ):R)*b) (X 0))=X 0
    simp only [hom_X0,map_add,map_mul,hom_C,hom_X1]
    simp only [map_neg]
    calc
      (C (((a⁻¹:Rˣ):R)) : Poly R) * (C (a:R) * X 0 + C b * X 1) +
          (-C (((a⁻¹:Rˣ):R))) * C b * X 1 =
          (C (((a⁻¹:Rˣ):R)) * C (a:R)) * X 0 := by ring
      _ = X 0 := by rw [← map_mul]; simp
  · change hom R a b (hom R a⁻¹ (-((a⁻¹:Rˣ):R)*b) (X 1))=X 1
    simp only [hom_X1]
lemma inverse_hom (a:Rˣ) (b:R):
    (hom R a⁻¹ (-((a⁻¹:Rˣ):R)*b)).comp (hom R a b)=AlgHom.id R (Poly R):=by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change hom R a⁻¹ (-((a⁻¹:Rˣ):R)*b) (hom R a b (X 0))=X 0
    simp only [hom_X0,map_add,map_mul,hom_C,hom_X1]
    simp only [map_neg]
    calc
      (C (a:R) : Poly R) * (C (((a⁻¹:Rˣ):R)) * X 0 +
          (-C (((a⁻¹:Rˣ):R))) * C b * X 1) + C b * X 1 =
          (C (a:R) * C (((a⁻¹:Rˣ):R))) * X 0 +
          (1 - C (a:R) * C (((a⁻¹:Rˣ):R))) * C b * X 1 := by ring
      _ = X 0 := by rw [← map_mul]; simp
  · change hom R a⁻¹ (-((a⁻¹:Rˣ):R)*b) (hom R a b (X 1))=X 1
    simp only [hom_X1]
end GradedAffineLine318
