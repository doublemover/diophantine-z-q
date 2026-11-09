module
public import ContactWholePrincipalReduction318
public import Mathlib.Tactic.FieldSimp

public section
noncomputable section
namespace ContactFinitePoleReduction318
attribute [-instance] DivisionRing.toRatAlgebra
open RootOrderMonomialBasis318 InfinityFieldCoordinates318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The number of original infinity ratios in this basis monomial. -/
@[expose] def weight (i : ThreeIndex) : ℕ := (i.1 : ℕ) + (i.2.1 : ℕ) + (i.2.2 : ℕ)

/-- Cancel the denominator of the ratio monomial against a sufficiently high
pole in u=b/a. No quotient or geometric dimension argument occurs here. -/
theorem pole_factor {F : Type*} [Field F] (a b x y z : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (p q r e : ℕ) :
    (a / b)^(p+q+r+e) * ((x/a)^p * (y/a)^q * (z/a)^r) =
      (b⁻¹)^(p+q+r+e) * a^e * x^p * y^q * z^r := by
  simp only [pow_add,div_pow]
  field_simp [ha,hb] <;> ring

variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (L c) := (KummerTensorField318.source_raw_field c).toField

@[expose] def finiteGenerator (j : Fin 4) : ContactKummerOrder318.SourceOrder c :=
  FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) j

theorem finiteGenerator_embedding (j : Fin 4) :
    ContactKummerOrder318.embedding c (finiteGenerator c j) = root c j :=
  FourRootSignBaseChange318.coefficientMap_generator
    (ContactKummerOrder318.coefficient c) (RatFunc ℚ) j

/-- The exact finite-chart polynomial witnessing a pole of order weight+e.
The normalization includes the original c0 to its full power. -/
@[expose] def finiteWitness (i : ThreeIndex) (e : ℕ) : ContactKummerOrder318.SourceOrder c :=
  algebraMap ℚ (ContactKummerOrder318.SourceOrder c) (((c 0 : ℚ)⁻¹)^(weight i+e)) *
    finiteGenerator c 0 ^ e * finiteGenerator c 1 ^ (i.1 : ℕ) *
    finiteGenerator c 2 ^ (i.2.1 : ℕ) * finiteGenerator c 3 ^ (i.2.2 : ℕ)

theorem finiteWitness_embedding (i : ThreeIndex) (e : ℕ) :
    ContactKummerOrder318.embedding c (finiteWitness c i e) =
      (algebraMap ℚ (L c) (c 0 : ℚ))⁻¹ ^ (weight i+e) * root c 0 ^ e *
        root c 1 ^ (i.1 : ℕ) * root c 2 ^ (i.2.1 : ℕ) * root c 3 ^ (i.2.2 : ℕ) := by
  simp only [finiteWitness,map_mul,map_pow,finiteGenerator_embedding,
    RingHom.map_rat_algebraMap,map_inv₀]

/-- Every pole at least as large as the ratio weight is exactly the image of
an element of the original finite chart, inside the original overlap ring. -/
theorem pole_at_weight_add (i : ThreeIndex) (e : ℕ) :
    ContactInfinityRegularFractions318.inverseU c ^ (weight i+e) *
        InfinityOverlapLocalization318.toOpen c (ContactHOneOrderBases318.infinityBasis c i) =
      SourceOpenFractionField318.orderToOpen c (finiteWitness c i e) := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  simp only [map_mul,map_pow,ContactInfinityRegularFractions318.inverse_u_embedding,
    InfinityOverlapLocalization318.toOpen_embedding,ContactHOneOrderBases318.infinity_embedding,
    SourceOpenFractionField318.openEmbedding_on_order,finiteWitness_embedding]
  simp only [u,ratio,inv_div]
  exact pole_factor (root c 0) (algebraMap ℚ (L c) (c 0 : ℚ)) (root c 1) (root c 2) (root c 3)
    (root_ne_zero c 0) (constant_ne_zero c (c 0).ne_zero)
    (i.1 : ℕ) (i.2.1 : ℕ) (i.2.2 : ℕ) e

theorem pole_of_weight_le (i : ThreeIndex) (k : ℕ) (hk : weight i ≤ k) :
    ContactInfinityRegularFractions318.inverseU c ^ k *
        InfinityOverlapLocalization318.toOpen c (ContactHOneOrderBases318.infinityBasis c i) =
      SourceOpenFractionField318.orderToOpen c (finiteWitness c i (k-weight i)) := by
  have h : weight i + (k-weight i) = k := by omega
  simpa only [h] using pole_at_weight_add c i (k-weight i)

end ContactFinitePoleReduction318
