module
public import PELOriginalReducedProjectiveCandidate318
public import ComplexProjectiveMarkerPoint318
public import PELOriginalHomogeneousRelationVanishing318
public section
noncomputable section
namespace PELOriginalProjectiveCandidatePoints318
open AlgebraicGeometry PELOriginalCubicRelationIdeal318
open PELOriginalReducedProjectiveCandidate318 PELOriginalAllLevelProjectiveMap318
open PELOriginalPolarizationTransitions318 PELOriginalLevelTheta318
variable (τ:ℂ) (hτ:0<τ.im)
local instance standardGrading:GradedAlgebra degrees:=MvPolynomial.gradedAlgebra
lemma actual_coordinate_nonzero(q:Base τ):∃j:Label 3,baseVector τ hτ 1 q j≠0:=by
  by_contra h
  push_neg at h
  exact baseVector_nonzero τ hτ 1 q (funext h)
/-- Actual homogeneous-prime point of the true projective Scheme,
constructed from the SAME nine original section coefficients. This is
an underlying scheme point, not yet a Spec(C)-valued morphism. -/
@[expose] def originalPoint(q:Base τ):ambient:=
  ComplexProjectiveMarkerPoint318.point (baseVector τ hτ 1 q)
    (actual_coordinate_nonzero τ hτ q)
lemma originalPoint_homogeneous(q:Base τ)(p:Equations)(n:ℕ)(hp:p.IsHomogeneous n):
    p∈(originalPoint τ hτ q).asHomogeneousIdeal↔
      MvPolynomial.eval (baseVector τ hτ 1 q) p=0:=
  ComplexProjectiveMarkerPoint318.homogeneous_mem_iff _ _ p n hp

/-- ALL relations vanish in the actual homogeneous-prime point, not
just one chosen finite equation list. Homogeneous components are
recovered from the actual graded section algebra before evaluation. -/
lemma relations_contained(q:Base τ):
    (relations τ hτ:Set Equations)⊆(originalPoint τ hτ q).asHomogeneousIdeal:=by
  intro p hp
  rw [←MvPolynomial.sum_homogeneousComponent p]
  apply (originalPoint τ hτ q).asHomogeneousIdeal.toIdeal.sum_mem
  intro n hn
  apply (originalPoint_homogeneous τ hτ q _ n
    (MvPolynomial.homogeneousComponent_mem n p)).mpr
  exact (PELOriginalHomogeneousRelationVanishing318.homogeneous_relation_iff τ hτ
    _ n (MvPolynomial.homogeneousComponent_mem n p)).mp
      (homogeneous_component_mem τ hτ p hp n) q
lemma originalPoint_in_candidate(q:Base τ):
    originalPoint τ hτ q∈Set.range (inclusion τ hτ):=
  (point_mem_iff τ hτ _).mpr (relations_contained τ hτ q)

/-- A point of the actual reduced closed subscheme above each original
analytic source point. Surjectivity onto the candidate is NOT asserted:
that would be part of the missing algebraic/analytic image theorem. -/
@[expose] def candidatePoint(q:Base τ):candidate τ hτ:=
  Classical.choose (originalPoint_in_candidate τ hτ q)
lemma candidatePoint_image(q:Base τ):
    inclusion τ hτ (candidatePoint τ hτ q)=originalPoint τ hτ q:=
  Classical.choose_spec (originalPoint_in_candidate τ hτ q)
lemma originalPoint_relations_iff(p:Equations)(n:ℕ)(hp:p.IsHomogeneous n):
    p∈relations τ hτ↔∀q:Base τ,p∈(originalPoint τ hτ q).asHomogeneousIdeal:=by
  rw [PELOriginalHomogeneousRelationVanishing318.homogeneous_relation_iff τ hτ p n hp]
  exact forall_congr' (fun q=>(originalPoint_homogeneous τ hτ q p n hp).symm)
end PELOriginalProjectiveCandidatePoints318
