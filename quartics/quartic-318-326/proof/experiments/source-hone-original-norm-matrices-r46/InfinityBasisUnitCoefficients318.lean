module
public import OriginalSimplePoleResidues318
public import SourceHOneCharacterIndices318

public section
noncomputable section
namespace InfinityBasisUnitCoefficients318
open RootOrderMonomialBasis318 ContactInfinityRegularFractions318
open SourceHOneCharacterIndices318
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

@[expose] def squareCoefficient (s : ThreeIndex) : Base c :=
  InfinityOrderCoordinates318.coefficient c 0 ^ (s.1 : ℕ) *
    InfinityOrderCoordinates318.coefficient c 1 ^ (s.2.1 : ℕ) *
    InfinityOrderCoordinates318.coefficient c 2 ^ (s.2.2 : ℕ)

theorem coefficient_unit (s : ThreeIndex) : IsUnit (squareCoefficient c s) :=
  (((InfinityOpenChart318.coefficient_unit c 0).pow _).mul
    ((InfinityOpenChart318.coefficient_unit c 1).pow _)).mul
    ((InfinityOpenChart318.coefficient_unit c 2).pow _)

theorem generator_square (j : Fin 3) : InfinityOrderCoordinates318.generator c j ^ 2 =
    algebraMap (Base c) (InfinityRing c) (InfinityOrderCoordinates318.coefficient c j) := by
  rw [InfinityOrderCoordinates318.generator_eq_ratio,InfinityCharacterUnits318.ratio_square]
  all_goals rfl

theorem basis_square (s : ThreeIndex) : ContactHOneOrderBases318.infinityBasis c s ^ 2 =
    algebraMap (Base c) (InfinityRing c) (squareCoefficient c s) := by
  change RootOrderMonomialBasis318.threeBasis (InfinityOrderCoordinates318.coefficient c) s ^ 2 = _
  rw [RootOrderMonomialBasis318.threeBasis_monomial]
  change (InfinityOrderCoordinates318.generator c 0 ^ (s.1 : ℕ) *
    InfinityOrderCoordinates318.generator c 1 ^ (s.2.1 : ℕ) *
    InfinityOrderCoordinates318.generator c 2 ^ (s.2.2 : ℕ)) ^ 2 = _
  rcases s with ⟨i,j,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [squareCoefficient,mul_pow,generator_square,Algebra.TensorProduct.one_def]

/-- The unit ratio product is exactly the named coordinate basis vector. -/
theorem ratioProduct_basis (i : Fin 4) : InfinityCharacterUnits318.ratioProduct c i =
    ContactHOneOrderBases318.infinityBasis c (smallIndex (some i)).val.1 := by
  have hb := RootOrderMonomialBasis318.threeBasis_monomial
    (InfinityOrderCoordinates318.coefficient c) (smallIndex (some i)).val.1
  change ContactHOneOrderBases318.infinityBasis c (smallIndex (some i)).val.1 =
    InfinityOrderCoordinates318.generator c 0 ^ ((smallIndex (some i)).val.1.1 : ℕ) *
    InfinityOrderCoordinates318.generator c 1 ^ ((smallIndex (some i)).val.1.2.1 : ℕ) *
    InfinityOrderCoordinates318.generator c 2 ^ ((smallIndex (some i)).val.1.2.2 : ℕ) at hb
  rw [hb]
  simp only [InfinityOrderCoordinates318.generator_eq_ratio]
  fin_cases i <;>
    simp [InfinityCharacterUnits318.ratioProduct,SourceCharacterFields318.complement_eq,SourceTwistArithmetic318.complement,
      InfinityCharacterUnits318.indexedRatio,smallIndex,Fin.prod_univ_succ,Fin.cases,Fin.induction,Fin.induction.go,mul_assoc]

/-- Unit coefficients remain nonzero under the original u=0 point. -/
theorem evaluated_inverse_ne_zero (s : ThreeIndex) :
    InfinityOpenChart318.infinityPoint c (((coefficient_unit c s).unit⁻¹ : (Base c)ˣ) : Base c) ≠ 0 :=
  (((coefficient_unit c s).unit⁻¹).isUnit.map (InfinityOpenChart318.infinityPoint c)).ne_zero

end InfinityBasisUnitCoefficients318
