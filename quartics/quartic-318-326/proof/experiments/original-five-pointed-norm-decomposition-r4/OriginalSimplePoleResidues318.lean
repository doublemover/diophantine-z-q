module
public import OriginalSmallPoleResidues318

public section
noncomputable section
namespace OriginalSimplePoleResidues318
open Polynomial RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open ContactWholePrincipalReduction318 OriginalInfinityCoefficient318 OriginalNegativePoleUniqueness318
open OriginalOverlapResidues318
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- Keep a prescribed pole bound rather than choosing another localization representation. -/
theorem prescribed_reduction (a : InfinityRing c) (n : ℕ) :
    ∃ R : ThreeIndex → ℚ[X], ∃ b : InfinityRing c,
      (∀ i, (R i).degree < (n : WithBot ℕ)) ∧
      inclusion c a * (inverseU c)^n =
        (∑ i, principalTerm c (R i) n * inclusion c (ContactHOneOrderBases318.infinityBasis c i)) +
          inclusion c b := by
  choose R b hR hb using fun i : ThreeIndex =>
    coefficient_principal_reduction c ((ContactHOneOrderBases318.infinityBasis c).repr a i) n
  refine ⟨R,∑ i, b i * ContactHOneOrderBases318.infinityBasis c i,hR,?_⟩
  have hterm (i : ThreeIndex) :
      inclusion c ((ContactHOneOrderBases318.infinityBasis c).repr a i •
        ContactHOneOrderBases318.infinityBasis c i) * (inverseU c)^n =
      principalTerm c (R i) n * inclusion c (ContactHOneOrderBases318.infinityBasis c i) +
        inclusion c (b i * ContactHOneOrderBases318.infinityBasis c i) := by
    rw [NativeTensorScalar318.three_smul (InfinityOrderCoordinates318.coefficient c),map_mul]
    calc
      inclusion c (algebraMap (Base c) (InfinityRing c)
          ((ContactHOneOrderBases318.infinityBasis c).repr a i)) *
          inclusion c (ContactHOneOrderBases318.infinityBasis c i) * (inverseU c)^n =
        (inclusion c (algebraMap (Base c) (InfinityRing c)
          ((ContactHOneOrderBases318.infinityBasis c).repr a i)) * (inverseU c)^n) *
          inclusion c (ContactHOneOrderBases318.infinityBasis c i) := by ring
      _ = _ := by
        change (InfinityOverlapLocalization318.toOpen c _ * (inverseU c)^n) * _ = _
        rw [hb i,add_mul,map_mul]
        all_goals rfl
  calc
    inclusion c a * (inverseU c)^n = inclusion c (∑ i, (ContactHOneOrderBases318.infinityBasis c).repr a i •
          ContactHOneOrderBases318.infinityBasis c i) * (inverseU c)^n := by
      rw [ContactHOneOrderBases318.infinity_expansion]
    _ = ∑ i, inclusion c ((ContactHOneOrderBases318.infinityBasis c).repr a i •
          ContactHOneOrderBases318.infinityBasis c i) * (inverseU c)^n := by
      rw [map_sum,Finset.sum_mul]
    _ = ∑ i, (principalTerm c (R i) n *
          inclusion c (ContactHOneOrderBases318.infinityBasis c i) +
          inclusion c (b i * ContactHOneOrderBases318.infinityBasis c i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = _ := by rw [Finset.sum_add_distrib,map_sum]


theorem degree_one_form (P : ℚ[X]) (hP : P.degree < (1 : WithBot ℕ)) : P = C (P.coeff 0) := by
  classical
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · have hz : P.coeff n = 0 := by
      by_contra hc
      have hh := ContactPrincipalCoefficientExpansion318.support_lt_pole P 1 hP n
        (Polynomial.mem_support_iff.mpr hc)
      omega
    simp [Polynomial.coeff_C,hn,hz]

/-- Every simple pole has a genuine original infinity-regular remainder. -/
theorem simple_reduction (a : InfinityRing c) :
    ∃ q : ThreeIndex → ℚ, ∃ b : InfinityRing c,
      inclusion c a * inverseU c = (∑ i, poleTerm c (q i) 1 i) + inclusion c b := by
  obtain ⟨R,b,hR,hr⟩ := prescribed_reduction c a 1
  refine ⟨fun i => (R i).coeff 0,b,?_⟩
  have ht (i : ThreeIndex) : principalTerm c (R i) 1 *
      inclusion c (ContactHOneOrderBases318.infinityBasis c i) = poleTerm c ((R i).coeff 0) 1 i := by
    conv_lhs => rw [degree_one_form (R i) (hR i)]
    change ContactPrincipalCoefficientExpansion318.polynomialMap c (C ((R i).coeff 0)) *
      (inverseU c)^1 * inclusion c (ContactHOneOrderBases318.infinityBasis c i) = _
    rw [ContactPrincipalCoefficientExpansion318.polynomialMap_C]
    rfl
  simpa only [pow_one,ht] using hr

/-- Multiplying a simple pole by the actual coordinate recovers its infinity constant terms. -/
theorem simple_coefficients (a b : InfinityRing c) (q : ThreeIndex → ℚ)
    (h : inclusion c a * inverseU c = (∑ i, poleTerm c (q i) 1 i) + inclusion c b)
    (i : ThreeIndex) : q i = zeroCoordinate c i a := by
  have hi : a = (∑ j, infinityTerm c (q j) 0 j) + b * coordinate c := by
    apply inclusion_injective c
    change inclusion c a = inclusion c ((∑ j, infinityTerm c (q j) 0 j) + b * coordinate c)
    calc
      inclusion c a = (inclusion c a * inverseU c) * SourceInfinityOverlap318.u c := by
        rw [mul_assoc,mul_comm (inverseU c),u_inverse,mul_one]
      _ = ((∑ j, poleTerm c (q j) 1 j) + inclusion c b) * SourceInfinityOverlap318.u c := by rw [h]
      _ = (∑ j, inclusion c (infinityTerm c (q j) 0 j)) +
          inclusion c b * SourceInfinityOverlap318.u c := by
        rw [add_mul,Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [pow_one,Nat.sub_self] using clear_poleTerm c (q j) 1 1 j le_rfl
      _ = _ := by simp only [map_add,map_sum,map_mul,inclusion_coordinate]
  have he := congrArg (zeroCoordinate c i) hi
  rw [map_add,zeroCoordinate_sum_terms] at he
  have hz : zeroCoordinate c i (b * coordinate c) = 0 := by
    rw [mul_comm,zeroCoordinate_coordinate_mul]
  simpa only [hz,ite_true,add_zero] using he.symm

/-- The first negative residue is the original infinity-basis coefficient evaluated at u=0. -/
theorem simple_residue (a : InfinityRing c) (i : ThreeIndex) :
    residues c (inclusion c a * inverseU c) (0,i) = zeroCoordinate c i a := by
  classical
  obtain ⟨q,b,h⟩ := simple_reduction c a
  have he : residues c (inclusion c a * inverseU c) = ∑ j, Finsupp.single (0,j) (q j) := by
    rw [h,map_add,map_sum]
    have hb : residues c (inclusion c b) = 0 := residues_infinity c b
    simp only [hb,add_zero,residues_pole c _ 1 _ (by decide),Nat.sub_self]
  rw [he]
  change (Finsupp.applyAddHom (0,i)) (∑ j, Finsupp.single (0,j) (q j)) = _
  rw [map_sum]
  change (∑ j, if (0,j) = (0,i) then q j else 0) = _
  simpa only [Prod.mk.injEq,true_and,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    using simple_coefficients c a b q h i

end OriginalSimplePoleResidues318
