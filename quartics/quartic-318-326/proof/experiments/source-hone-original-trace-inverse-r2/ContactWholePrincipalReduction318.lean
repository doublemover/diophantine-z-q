module
public import NativeTensorScalar318
public import ContactHOneOrderBases318
public import ContactInfinityRegularFractions318

public section
noncomputable section
namespace ContactWholePrincipalReduction318
open Polynomial RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

@[expose] def inclusion : InfinityRing c →+* OverlapRing c :=
  InfinityOverlapLocalization318.toOpen c

/-- The chosen actual overlap inverse has the original multiplicative identity. -/
theorem u_inverse : SourceInfinityOverlap318.u c * inverseU c = 1 := by
  rw [← (SourceInfinityOverlap318.u_unit c).unit_spec]
  exact (SourceInfinityOverlap318.u_unit c).unit.mul_inv

/-- Every element of the entire original overlap ring has a pole only along
u when regarded over the actual infinity order. -/
theorem overlap_fraction (z : OverlapRing c) :
    ∃ n : ℕ, ∃ a : InfinityRing c, z = inclusion c a * (inverseU c)^n := by
  letI : Algebra (InfinityRing c) (OverlapRing c) := (inclusion c).toAlgebra
  letI : IsLocalization.Away (InfinityOverlapLocalization318.coordinate c) (OverlapRing c) :=
    SourceInfinityOverlap318.whole_localization c
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj
    (InfinityOverlapLocalization318.coordinate c) z
  change z * (SourceInfinityOverlap318.u c)^n = inclusion c a at ha
  have hu : (SourceInfinityOverlap318.u c)^n * (inverseU c)^n = 1 := by
    rw [← mul_pow,u_inverse,one_pow]
  refine ⟨n,a,?_⟩
  calc
    z = z * ((SourceInfinityOverlap318.u c)^n * (inverseU c)^n) := by rw [hu,mul_one]
    _ = (z * (SourceInfinityOverlap318.u c)^n) * (inverseU c)^n := by ring
    _ = inclusion c a * (inverseU c)^n := by rw [ha]

/-- Full eight-monomial reduction in the actual overlap ring. The remaining
infinity-regular term is an actual element of the original infinity ring. -/
theorem reduction (z : OverlapRing c) :
    ∃ n : ℕ, ∃ R : ThreeIndex → ℚ[X], ∃ b : InfinityRing c,
      (∀ i, (R i).degree < (n : WithBot ℕ)) ∧
      z = (∑ i, principalTerm c (R i) n * inclusion c (ContactHOneOrderBases318.infinityBasis c i)) +
        inclusion c b := by
  obtain ⟨n,a,ha⟩ := overlap_fraction c z
  choose R b hR hb using fun i : ThreeIndex =>
    coefficient_principal_reduction c ((ContactHOneOrderBases318.infinityBasis c).repr a i) n
  refine ⟨n,R,∑ i, b i * ContactHOneOrderBases318.infinityBasis c i,hR,?_⟩
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
  calc
    z = inclusion c a * (inverseU c)^n := ha
    _ = inclusion c (∑ i, (ContactHOneOrderBases318.infinityBasis c).repr a i •
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

end ContactWholePrincipalReduction318
