module
public import ThreeTorsionIdentity318
public section
noncomputable section
namespace ShortThreeTorsion318
open Polynomial
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R] (A B:R) [Invertible (3:R)]

@[expose] def polynomial : R[X] :=
  X^4+C (2*A)*X^2+C (4*B)*X-C (⅟ (3:R)*A^2)

lemma monic : (polynomial A B).Monic := by
  unfold polynomial
  monicity!

lemma degree [Nontrivial R] : (polynomial A B).natDegree=4 := by
  unfold polynomial
  compute_degree!

lemma scalar_identity : C (3:R)*polynomial A B=
    ThreeTorsionIdentity318.divisionPolynomial A B := by
  have hi:=congrArg (C:R→+*R[X]) (mul_invOf_self (3:R))
  simp only [map_mul,map_one,map_ofNat] at hi
  simp only [polynomial,ThreeTorsionIdentity318.divisionPolynomial,map_mul,map_pow,map_ofNat]
  linear_combination -C A^2*hi

lemma separable (hD:IsUnit (-16*(4*A^3+27*B^2))) : (polynomial A B).Separable := by
  have hd:IsUnit (4*A^3+27*B^2):=(IsUnit.mul_iff.mp hD).2
  obtain ⟨u,hu⟩:=hd
  have hc:IsCoprime (ThreeTorsionIdentity318.divisionPolynomial A B)
      (ShortTwoTorsion318.polynomial A B) := by
    refine ⟨C (↑u⁻¹:R)*(-C (4*A)-3*X^2),
      C (↑u⁻¹:R)*(3*(C (7*A)*X+C (9*B)+3*X^3)),?_⟩
    rw [mul_assoc,mul_assoc,←mul_add,ThreeTorsionIdentity318.bezout,←hu,
      ←C_mul,Units.inv_mul,C_1]
  have h4:IsUnit (4:R):=by
    have h16:IsUnit (16:R):=by simpa only [neg_neg] using ((IsUnit.mul_iff.mp hD).1).neg
    apply (isUnit_pow_iff (by decide:2≠0)).mp
    convert h16 using 1 <;> norm_num
  have h12:IsUnit (12:R):=by
    convert (isUnit_of_invertible (3:R)).mul h4 using 1 <;> norm_num
  have hs:(ThreeTorsionIdentity318.divisionPolynomial A B).Separable:=by
    rw [Polynomial.separable_def,ThreeTorsionIdentity318.derivative]
    exact (isCoprime_mul_unit_left_right (h12.map C) _ _).mpr hc
  rw [←scalar_identity A B] at hs
  exact hs.of_mul_right

abbrev Ring := AdjoinRoot (polynomial A B)

lemma finite : Module.Finite R (Ring A B) := (monic A B).finite_adjoinRoot
lemma free : Module.Free R (Ring A B) := (monic A B).free_adjoinRoot
lemma etale (hD:IsUnit (-16*(4*A^3+27*B^2))) : Algebra.Etale R (Ring A B) :=
  MonicRootEtale318.root_etale _ (monic A B) (separable A B hD)
lemma faithfullyFlat [Nontrivial R] : Module.FaithfullyFlat R (Ring A B) :=
  MonicRootEtale318.root_faithfullyFlat _ (monic A B) (by rw [degree];decide)
lemma rank_four [Nontrivial R] : Module.finrank R (Ring A B)=4 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' (monic A B)).basis,Fintype.card_fin]
  exact degree A B

@[expose] def splitting [Nontrivial R] (hD:IsUnit (-16*(4*A^3+27*B^2))) :=
  MonicEtaleSplitting318.splitting (polynomial A B) (monic A B) (separable A B hD)

lemma division_zero :
    AdjoinRoot.mk (polynomial A B) (ThreeTorsionIdentity318.divisionPolynomial A B)=0 := by
  rw [←scalar_identity,map_mul,AdjoinRoot.mk_self,mul_zero]

lemma cubic_unit (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    IsUnit (AdjoinRoot.mk (polynomial A B) (ShortTwoTorsion318.polynomial A B)) := by
  have hh:=congrArg (AdjoinRoot.mk (polynomial A B)) (ThreeTorsionIdentity318.bezout A B)
  rw [map_add,map_mul,map_mul,division_zero,mul_zero,zero_add,AdjoinRoot.mk_C] at hh
  have hu:IsUnit (AdjoinRoot.of (polynomial A B) (4*A^3+27*B^2)):=
    ((IsUnit.mul_iff.mp hD).2).map _
  rw [←hh,map_mul] at hu
  exact (IsUnit.mul_iff.mp hu).2

end ShortThreeTorsion318
