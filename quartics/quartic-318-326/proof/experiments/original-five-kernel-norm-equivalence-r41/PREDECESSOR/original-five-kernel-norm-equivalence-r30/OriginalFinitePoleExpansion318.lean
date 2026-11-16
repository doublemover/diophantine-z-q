module
public import OriginalOverlapResidues318
public import ContactFinitePoleReduction318
public import NativeTensorScalar318

public section
noncomputable section
namespace OriginalFinitePoleExpansion318
attribute [-instance] DivisionRing.toRatAlgebra
open RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open ContactFinitePoleReduction318 OriginalNegativePoleUniqueness318
open InfinityFieldCoordinates318 Polynomial
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (L c) := (KummerTensorField318.source_raw_field c).toField

@[expose] def dropZero (s : FourIndex) : ThreeIndex := (s.1.2,(s.2.1,s.2.2))
@[expose] def totalWeight (s : FourIndex) : ℕ :=
  (s.1.1 : ℕ) + (s.1.2 : ℕ) + (s.2.1 : ℕ) + (s.2.2 : ℕ)

theorem weight_drop_le (s : FourIndex) : weight (dropZero s) ≤ totalWeight s := by
  change (s.1.2 : ℕ) + (s.2.1 : ℕ) + (s.2.2 : ℕ) ≤
    (s.1.1 : ℕ) + (s.1.2 : ℕ) + (s.2.1 : ℕ) + (s.2.2 : ℕ)
  omega

theorem finite_root_zero :
    SourceOpenFractionField318.orderToOpen c (finiteGenerator c 0) =
      algebraMap ℚ (OverlapRing c) (c 0 : ℚ) * inverseU c := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  rw [SourceOpenFractionField318.openEmbedding_on_order,finiteGenerator_embedding,
    map_mul,RingHom.map_rat_algebraMap,ContactInfinityRegularFractions318.inverse_u_embedding]
  have h : root c 0 = algebraMap ℚ (L c) (c 0 : ℚ) / u c := recover_root_zero c
  simpa only [div_eq_mul_inv] using h

theorem finite_root_other (j : Fin 3) :
    SourceOpenFractionField318.orderToOpen c (finiteGenerator c j.succ) =
      algebraMap ℚ (OverlapRing c) (c 0 : ℚ) * inverseU c *
        InfinityOverlapLocalization318.toOpen c (InfinityOrderCoordinates318.generator c j) := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  rw [SourceOpenFractionField318.openEmbedding_on_order,finiteGenerator_embedding,
    map_mul,map_mul,RingHom.map_rat_algebraMap,ContactInfinityRegularFractions318.inverse_u_embedding,
    InfinityOverlapLocalization318.toOpen_embedding,InfinityOrderCoordinates318.generator_embedding]
  have h : root c j.succ = algebraMap ℚ (L c) (c 0 : ℚ) / u c * ratio c j := recover_root c j
  simpa only [div_eq_mul_inv] using h

theorem finite_t :
    SourceOpenFractionField318.orderToOpen c
      (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) X) =
      algebraMap ℚ (OverlapRing c) (c 0 : ℚ) * (inverseU c)^2 := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  rw [SourceOpenFractionField318.openEmbedding_on_order,SourceFractionField318.embedding_on_polynomial,
    RatFunc.algebraMap_X,map_mul,RingHom.map_rat_algebraMap,map_pow,
    ContactInfinityRegularFractions318.inverse_u_embedding]
  have h : algebraMap (RatFunc ℚ) (L c) RatFunc.X =
      algebraMap ℚ (L c) (c 0 : ℚ) / u c ^ 2 := recover_t c
  simpa only [div_eq_mul_inv, inv_pow] using h

/-- Every original finite tensor monomial has an exact negative-power expansion
in the original infinity monomial, with its full c0 power retained. -/
theorem finite_basis_to_pole (s : FourIndex) :
    SourceOpenFractionField318.orderToOpen c (ContactHOneOrderBases318.finiteBasis c s) =
      poleTerm c ((c 0 : ℚ)^(totalWeight s)) (totalWeight s) (dropZero s) := by
  change SourceOpenFractionField318.orderToOpen c
    (fourBasis (ContactKummerOrder318.coefficient c) s) = _
  rw [fourBasis_monomial]
  simp only [map_mul,map_pow]
  change SourceOpenFractionField318.orderToOpen c (finiteGenerator c 0) ^ (s.1.1 : ℕ) *
    SourceOpenFractionField318.orderToOpen c (finiteGenerator c (0 : Fin 3).succ) ^ (s.1.2 : ℕ) *
    SourceOpenFractionField318.orderToOpen c (finiteGenerator c (1 : Fin 3).succ) ^ (s.2.1 : ℕ) *
    SourceOpenFractionField318.orderToOpen c (finiteGenerator c (2 : Fin 3).succ) ^ (s.2.2 : ℕ) = _
  rw [finite_root_zero,finite_root_other c 0,finite_root_other c 1,finite_root_other c 2]
  have hinfinity (i : ThreeIndex) :
      InfinityOverlapLocalization318.toOpen c (ContactHOneOrderBases318.infinityBasis c i) =
        InfinityOverlapLocalization318.toOpen c (InfinityOrderCoordinates318.generator c 0) ^ (i.1 : ℕ) *
        InfinityOverlapLocalization318.toOpen c (InfinityOrderCoordinates318.generator c 1) ^ (i.2.1 : ℕ) *
        InfinityOverlapLocalization318.toOpen c (InfinityOrderCoordinates318.generator c 2) ^ (i.2.2 : ℕ) := by
    change InfinityOverlapLocalization318.toOpen c
      (threeBasis (InfinityOrderCoordinates318.coefficient c) i) = _
    rw [threeBasis_monomial]
    simp only [map_mul, map_pow]
    all_goals rfl
  rw [poleTerm, hinfinity]
  simp only [map_mul,map_pow,totalWeight,dropZero,pow_add,mul_pow]
  ring

private theorem finite_constant (q : ℚ) :
    SourceOpenFractionField318.orderToOpen c
      (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) (C q)) =
        algebraMap ℚ (OverlapRing c) q :=
  RingHom.map_rat_algebraMap ((SourceOpenFractionField318.orderToOpen c).comp
    (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c))) q

/-- The original four-root tensor module, not a replacement scalar instance. -/
private theorem finite_smul (P : ℚ[X]) (z : ContactKummerOrder318.SourceOrder c) :
    P • z = algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) P * z :=
  NativeTensorScalar318.tensor_smul P z

theorem finite_coefficient_monomial (s : FourIndex) (q : ℚ) (m : ℕ) :
    SourceOpenFractionField318.orderToOpen c
      (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) (C q * X^m) *
        ContactHOneOrderBases318.finiteBasis c s) =
      poleTerm c (q * (c 0 : ℚ)^(m+totalWeight s)) (2*m+totalWeight s) (dropZero s) := by
  simp only [map_mul,map_pow]
  rw [finite_constant,finite_t,finite_basis_to_pole]
  simp only [poleTerm,map_mul,map_pow,pow_add,pow_mul,mul_pow]
  ring

/-- Complete polynomial-coefficient expansion of every original finite-chart
element. Every resulting pole has order at least its infinity monomial weight. -/
theorem finite_expansion (a : ContactKummerOrder318.SourceOrder c) :
    SourceOpenFractionField318.orderToOpen c a =
      ∑ s : FourIndex, ∑ m ∈ ((ContactHOneOrderBases318.finiteBasis c).repr a s).support,
        poleTerm c (((ContactHOneOrderBases318.finiteBasis c).repr a s).coeff m *
          (c 0 : ℚ)^(m+totalWeight s)) (2*m+totalWeight s) (dropZero s) := by
  calc
    _ = SourceOpenFractionField318.orderToOpen c (∑ s,
        (ContactHOneOrderBases318.finiteBasis c).repr a s • ContactHOneOrderBases318.finiteBasis c s) := by
      rw [ContactHOneOrderBases318.finite_expansion]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s _
      let P := (ContactHOneOrderBases318.finiteBasis c).repr a s
      have hP : (∑ m ∈ P.support, C (P.coeff m) * X^m) = P := sum_C_mul_X_pow_eq P
      rw [finite_smul c]
      change SourceOpenFractionField318.orderToOpen c
        (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) P *
          ContactHOneOrderBases318.finiteBasis c s) = _
      conv_lhs => rw [← hP]
      rw [map_sum,Finset.sum_mul,map_sum]
      apply Finset.sum_congr rfl
      intro m _
      exact finite_coefficient_monomial c s (P.coeff m) m

end OriginalFinitePoleExpansion318
