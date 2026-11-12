module
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic
public section
noncomputable section
namespace ProjectiveJLine318
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R]
abbrev grading := homogeneousSubmodule (Fin 2) R

@[expose] def zeroEquiv : R ≃+* grading R 0 where
  toFun r := ⟨C r,isHomogeneous_C _ r⟩
  invFun p := p.1.coeff 0
  left_inv r := by simp
  right_inv p := by
    apply Subtype.ext
    have h : p.1.totalDegree=0 := (totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.2
    exact (totalDegree_eq_zero_iff_eq_C.mp h).symm
  map_mul' a b := Subtype.ext (map_mul C a b)
  map_add' a b := Subtype.ext (map_add C a b)

instance zeroTower : IsScalarTower R (grading R 0) (MvPolynomial (Fin 2) R) where
  smul_assoc r a b := by
    change (r • (a: MvPolynomial (Fin 2) R))*b=r • ((a: MvPolynomial (Fin 2) R)*b)
    exact smul_mul_assoc r (a: MvPolynomial (Fin 2) R) b

/-- The actual ambient projective line is Mathlib's homogeneous Proj. -/
abbrev scheme : Scheme := AlgebraicGeometry.Proj (grading R)
/-- Its actual structure map, with degree-zero constants identified with R. -/
@[expose] def structureMap : scheme R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grading R) ≫ Spec.map (zeroEquiv R).toCommRingCatIso.hom

instance finiteType : Algebra.FiniteType (grading R 0) (MvPolynomial (Fin 2) R) := by
  apply Algebra.FiniteType.of_restrictScalars_finiteType R

instance structure_proper : IsProper (structureMap R) := by
  unfold structureMap
  infer_instance

end ProjectiveJLine318
