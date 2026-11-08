module
public import MonogenicSplitEquiv318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public section
noncomputable section
namespace ShortTwoTorsion318
open Polynomial
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] (A B:R)

@[expose] def polynomial : R[X] := X^3+C A*X+C B

lemma monic : (polynomial A B).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one 3
  · simpa only [polynomial,map_one,map_zero,one_mul,zero_mul,add_zero] using
      (Polynomial.natDegree_cubic_le (a:=(1:R)) (b:=0) (c:=A) (d:=B))
  · simp [polynomial]

lemma degree [Nontrivial R] : (polynomial A B).natDegree=3 := by
  convert Polynomial.natDegree_cubic (R:=R) (a:=1) (b:=0) (c:=A) (d:=B) one_ne_zero using 1 <;>
    simp [polynomial]

/-- The explicit cubic discriminant Bezout identity. -/
lemma bezout :
    (C (27*B)-C (18*A)*X)*polynomial A B+
      (C (6*A)*X^2-C (9*B)*X+C (4*A^2))*(polynomial A B).derivative=
        C (4*A^3+27*B^2) := by
  simp only [polynomial,derivative_add,derivative_pow,derivative_X,derivative_C,
    derivative_mul,map_add,map_mul,map_pow,map_ofNat,map_natCast]
  norm_num
  ring

lemma separable (hD:IsUnit (-16*(4*A^3+27*B^2))) : (polynomial A B).Separable := by
  have hd:IsUnit (4*A^3+27*B^2):=(IsUnit.mul_iff.mp hD).2
  obtain ⟨u,hu⟩:=hd
  refine ⟨C (↑u⁻¹:R)*(C (27*B)-C (18*A)*X),
    C (↑u⁻¹:R)*(C (6*A)*X^2-C (9*B)*X+C (4*A^2)),?_⟩
  rw [mul_assoc,mul_assoc,←mul_add,bezout,←hu,←C_mul,Units.inv_mul,C_1]

abbrev Ring := AdjoinRoot (polynomial A B)

lemma finite : Module.Finite R (Ring A B) := (monic A B).finite_adjoinRoot
lemma free : Module.Free R (Ring A B) := (monic A B).free_adjoinRoot
lemma etale (hD:IsUnit (-16*(4*A^3+27*B^2))) : Algebra.Etale R (Ring A B) :=
  MonicRootEtale318.root_etale _ (monic A B) (separable A B hD)
lemma faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Ring A B) :=
  MonicRootEtale318.root_faithfullyFlat _ (monic A B) (by rw [degree];decide)
lemma rank_three [Nontrivial R] : Module.finrank R (Ring A B)=3 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' (monic A B)).basis,Fintype.card_fin]
  exact degree A B

@[expose] def splitting [Nontrivial R] (hD:IsUnit (-16*(4*A^3+27*B^2))) :=
  MonicEtaleSplitting318.splitting (polynomial A B) (monic A B) (separable A B hD)

end ShortTwoTorsion318
