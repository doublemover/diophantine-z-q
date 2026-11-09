module
public import ContactPrincipalCoefficientExpansion318

public section
noncomputable section
namespace OriginalInfinityCoefficient318
open RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

@[expose] def baseU : Base c := algebraMap ℚ[X] (Base c) Polynomial.X
@[expose] def coordinate : InfinityRing c := InfinityOverlapLocalization318.coordinate c

@[expose] def zeroCoordinate (i : ThreeIndex) : InfinityRing c →+ ℚ where
  toFun b := InfinityOpenChart318.infinityPoint c ((ContactHOneOrderBases318.infinityBasis c).repr b i)
  map_zero' := by simp
  map_add' a b := by simp

theorem zeroCoordinate_smul_basis (i j : ThreeIndex) (a : Base c) :
    zeroCoordinate c i (a • ContactHOneOrderBases318.infinityBasis c j) =
      if j = i then InfinityOpenChart318.infinityPoint c a else 0 := by
  classical
  change InfinityOpenChart318.infinityPoint c
    ((ContactHOneOrderBases318.infinityBasis c).repr
      (a • ContactHOneOrderBases318.infinityBasis c j) i) = _
  simp only [map_smul,Module.Basis.repr_self,Finsupp.smul_apply,Finsupp.single_apply,smul_eq_mul]
  by_cases h : j = i <;> simp [h]

theorem zeroCoordinate_coordinate_mul (i : ThreeIndex) (b : InfinityRing c) :
    zeroCoordinate c i (coordinate c * b) = 0 := by
  have hs : coordinate c * b = baseU c • b := by
    rw [NativeTensorScalar318.three_smul (InfinityOrderCoordinates318.coefficient c)]
    rfl
  change InfinityOpenChart318.infinityPoint c
    ((ContactHOneOrderBases318.infinityBasis c).repr (coordinate c * b) i) = 0
  rw [hs]
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul,map_mul,baseU,
    InfinityOpenChart318.infinityPoint_on_base,Polynomial.eval_X,zero_mul]

@[expose] def infinityTerm (q : ℚ) (e : ℕ) (i : ThreeIndex) : InfinityRing c :=
  algebraMap ℚ (InfinityRing c) q * (coordinate c)^e * ContactHOneOrderBases318.infinityBasis c i

theorem infinityTerm_smul (q : ℚ) (e : ℕ) (i : ThreeIndex) :
    infinityTerm c q e i =
      (algebraMap ℚ (Base c) q * (baseU c)^e) • ContactHOneOrderBases318.infinityBasis c i := by
  rw [NativeTensorScalar318.three_smul (InfinityOrderCoordinates318.coefficient c)]
  rw [map_mul,map_pow,RingHom.map_rat_algebraMap] <;> rfl

theorem zeroCoordinate_term (i j : ThreeIndex) (q : ℚ) (e : ℕ) :
    zeroCoordinate c i (infinityTerm c q e j) = if j = i then (if e = 0 then q else 0) else 0 := by
  rw [infinityTerm_smul,zeroCoordinate_smul_basis]
  by_cases hji : j = i <;> by_cases he : e = 0 <;>
    simp [hji,he,map_mul,map_pow,baseU,InfinityOpenChart318.infinityPoint_on_base,
      RingHom.map_rat_algebraMap]

theorem zeroCoordinate_sum_terms (i : ThreeIndex) (q : ThreeIndex → ℚ) (e : ℕ) :
    zeroCoordinate c i (∑ j, infinityTerm c (q j) e j) = if e = 0 then q i else 0 := by
  classical
  simp only [map_sum,zeroCoordinate_term]
  simp

theorem zeroCoordinate_mul_coordinate_succ (i : ThreeIndex) (b : InfinityRing c) (n : ℕ) :
    zeroCoordinate c i (b * (coordinate c)^(n+1)) = 0 := by
  have h : b * (coordinate c)^(n+1) = coordinate c * (b * (coordinate c)^n) := by
    rw [pow_succ]
    ring
  rw [h,zeroCoordinate_coordinate_mul]

theorem inclusion_injective : Function.Injective (InfinityOverlapLocalization318.toOpen c) := by
  intro a b h
  apply InfinityOpenFractionField318.openEmbedding_injective c
  have he := congrArg (SourceOpenFractionField318.openEmbedding c) h
  simpa only [InfinityOverlapLocalization318.toOpen_embedding] using he

theorem inclusion_coordinate :
    InfinityOverlapLocalization318.toOpen c (coordinate c) = SourceInfinityOverlap318.u c := rfl

theorem inclusion_term (q : ℚ) (e : ℕ) (i : ThreeIndex) :
    InfinityOverlapLocalization318.toOpen c (infinityTerm c q e i) =
      algebraMap ℚ (OverlapRing c) q * (SourceInfinityOverlap318.u c)^e *
        InfinityOverlapLocalization318.toOpen c (ContactHOneOrderBases318.infinityBasis c i) := by
  simp only [infinityTerm,map_mul,map_pow,RingHom.map_rat_algebraMap,inclusion_coordinate]

end OriginalInfinityCoefficient318
