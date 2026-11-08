module
public import CompletedAdditionAssociativityTest318
public import CubicClosedImmersion318
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public section
noncomputable section
namespace CompletedAdditionAssociativity318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CompletedAdditionTriple318
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
/-- Reducedness of the original literal triple product promotes the exact
residue-field tests to equality of the actual associativity morphisms. -/
theorem associative_of_reduced [IsReduced (triple A B)] :
    leftAssociate A B hD=rightAssociate A B hD := by
  letI:=CubicClosedImmersion318.structure_proper A B
  apply AlgebraicGeometry.ext_of_fromSpecResidueField_eq _ _
    (WeierstrassGluing318.structureMap A B) Set.univ dense_univ
  · intro x _
    let t:Spec ((triple A B).residueField x) ⟶ triple A B:=(triple A B).fromSpecResidueField x
    obtain ⟨b,hb⟩:=Spec.map_surjective (t ≫ first A B ≫ WeierstrassGluing318.structureMap A B)
    letI : Algebra (OpenJModel318.Base N) ((triple A B).residueField x):=b.hom.toAlgebra
    exact CompletedAdditionAssociativityTest318.field_test N (K:=((triple A B).residueField x)) t hb.symm
  · rw [leftAssociate_base,rightAssociate_base]
end CompletedAdditionAssociativity318
