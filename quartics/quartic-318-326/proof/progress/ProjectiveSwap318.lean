module
public import ProjectiveAffineCharts318
public section
noncomputable section
namespace ProjectiveSwap318
open MvPolynomial Graded HomogeneousIdeal AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (R:Type*) [CommRing R]
abbrev Poly:=MvPolynomial (Fin 2) R
abbrev grading:=ProjectiveJLine318.grading R
@[expose] def variableImage (i:Fin 2):Poly R:=if i=0 then X 1 else X 0
@[expose] def hom:Poly R→ₐ[R]Poly R:=aeval (variableImage R)
@[simp] theorem hom_X0:hom R (X 0)=X 1:=by simp [hom,variableImage]
@[simp] theorem hom_X1:hom R (X 1)=X 0:=by simp [hom,variableImage]
@[simp] theorem hom_C (r:R):hom R (C r)=C r:=by simp [hom]
lemma variable_homogeneous (i:Fin 2):(variableImage R i).IsHomogeneous 1:=by
  fin_cases i <;> simp only [variableImage,Fin.reduceFinMk,ite_true,Fin.zero_eta,Fin.isValue]
  · exact isHomogeneous_X R 1
  · exact isHomogeneous_X R 0
@[expose] def gh:grading R→+*ᵍ grading R where
  __ := (hom R).toRingHom
  map_mem {i} {p} hp:=by
    change (hom R p).IsHomogeneous i
    simpa only [hom,one_mul] using (show p.IsHomogeneous i from hp).aeval
      (variableImage R) (variable_homogeneous R)
lemma gh_X0:gh R (X 0)=X 1:=hom_X0 R
lemma gh_X1:gh R (X 1)=X 0:=hom_X1 R
lemma gh_C (r:R):gh R (C r)=C r:=hom_C R r
lemma hom_twice:(hom R).comp (hom R)=AlgHom.id R (Poly R):=by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change hom R (hom R (X 0))=X 0
    rw [hom_X0,hom_X1]
  · change hom R (hom R (X 1))=X 1
    rw [hom_X1,hom_X0]
lemma gh_twice:(gh R).comp (gh R)=.id (grading R):=by
  apply GradedRingHom.ext
  intro p
  exact congrArg (fun f:Poly R→ₐ[R]Poly R=>f p) (hom_twice R)
lemma irrelevant_le:(grading R)₊≤(grading R)₊.map (gh R):=by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro i hi p hp
  have hm:gh R p∈(grading R)₊:=mem_irrelevant_of_mem _ hi (Graded.map_mem _ hp)
  have h:=Ideal.mem_map_of_mem (gh R).toRingHom hm
  have he:gh R (gh R p)=p:=congrArg (fun f:grading R→+*ᵍ grading R=>f p) (gh_twice R)
  change gh R (gh R p)∈((grading R)₊.map (gh R)).toIdeal at h
  rwa [he] at h
@[expose] def map:ProjectiveJLine318.scheme R⟶ProjectiveJLine318.scheme R:=Proj.map (gh R) (irrelevant_le R)
lemma map_twice:map R≫map R=𝟙 _:=by
  unfold map
  rw [←Proj.map_comp]
  simp only [gh_twice,Proj.map_id]
@[expose] def iso:ProjectiveJLine318.scheme R≅ProjectiveJLine318.scheme R where
  hom:=map R
  inv:=map R
  hom_inv_id:=map_twice R
  inv_hom_id:=map_twice R
end ProjectiveSwap318
