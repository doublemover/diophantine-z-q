module
public import ConcreteOriginalSixteenDenominator318
public import CanonicalJacobiNorm318
public import SelectedRayEmbeddings318
public section
namespace GaussianFixedRayConcretePrime318
lemma rational_prime : Nat.Prime 9649 := by norm_num
local instance : Fact (Nat.Prime 9649) := ⟨rational_prime⟩
lemma full_ray : GaussianRayQuadratic318.Ray 9649 57 80 := by
  norm_num [GaussianRayQuadratic318.Ray]
lemma residues : (57:ℤ)%7=1 ∧ (80:ℤ)%7=3 := by norm_num
lemma finite_roots : (1743:ZMod 9649)^8= -1 ∧ (1075:ZMod 9649)^4=2 := by
  norm_num
lemma quarter_values : GaussianNeighborNorms318.minus 57 80=9536 ∧
    GaussianNeighborNorms318.plus 57 80=9764 := by
  norm_num [GaussianNeighborNorms318.minus,GaussianNeighborNorms318.plus,GaussianNeighborNorms318.norm]
end GaussianFixedRayConcretePrime318
