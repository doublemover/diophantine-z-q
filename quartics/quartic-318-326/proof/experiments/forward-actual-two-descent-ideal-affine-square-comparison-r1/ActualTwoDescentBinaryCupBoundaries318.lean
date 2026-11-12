module
public import ActualTwoDescentBinaryCupCocycles318
public section
noncomputable section
namespace ActualTwoDescentBinaryCupBoundaries318
open ActualTwoDescentSquareOneBinary318 ActualTwoDescentBinarySymplectic318
open ActualTwoDescentBinaryCupCocycles318 groupCohomology
variable {G : Type*} [Group G]

def binarySelfCochain (α : G →* Multiplicative BinaryPlane) (g : G) : ZMod 2 :=
  binaryQuadratic (α g).toAdd

/-- An actual degree-one cochain, not an asserted cohomology cancellation. -/
lemma actual_binary_self_cup_boundary (α : G →* Multiplicative BinaryPlane) :
    d₁₂ (binaryCoefficientRep G) (binarySelfCochain α)=binaryCup α α := by
  funext g
  rcases g with ⟨g,h⟩
  change (binaryCoefficientRep G).ρ g (binaryQuadratic (α h).toAdd)-
    binaryQuadratic (α (g*h)).toAdd+binaryQuadratic (α g).toAdd=
    binaryPairing (α g).toAdd (α h).toAdd
  rw [Representation.isTrivial_apply,map_mul]
  exact actual_binary_quadratic_polar (α g).toAdd (α h).toAdd

lemma actual_binary_self_cochain_locally_constant [TopologicalSpace G]
    (α : G →* Multiplicative BinaryPlane) (hα : IsLocallyConstant α) :
    IsLocallyConstant (binarySelfCochain α) := hα.comp (fun z => binaryQuadratic z.toAdd)

lemma actual_binary_cup_class_alternating (α : G →* Multiplicative BinaryPlane) :
    binaryCupClass α α=0 := by
  apply (H2π_eq_zero_iff _).mpr
  exact ⟨binarySelfCochain α,actual_binary_self_cup_boundary α⟩

def binaryCrossCochain (α β : G →* Multiplicative BinaryPlane) (g : G) : ZMod 2 :=
  binaryPairing (α g).toAdd (β g).toAdd

lemma actual_binary_cross_boundary (α β : G →* Multiplicative BinaryPlane) :
    d₁₂ (binaryCoefficientRep G) (binaryCrossCochain α β)=binaryCup α β-binaryCup β α := by
  funext g
  rcases g with ⟨g,h⟩
  change (binaryCoefficientRep G).ρ g (binaryPairing (α h).toAdd (β h).toAdd)-
    binaryPairing (α (g*h)).toAdd (β (g*h)).toAdd+
    binaryPairing (α g).toAdd (β g).toAdd=
    binaryPairing (α g).toAdd (β h).toAdd-binaryPairing (β g).toAdd (α h).toAdd
  rw [Representation.isTrivial_apply,map_mul,map_mul]
  change binaryPairing (α h).toAdd (β h).toAdd-
    binaryPairing ((α g).toAdd+(α h).toAdd) ((β g).toAdd+(β h).toAdd)+
    binaryPairing (α g).toAdd (β g).toAdd=_
  rw [actual_binary_pairing_add_left,actual_binary_pairing_add_right,
    actual_binary_pairing_add_right,actual_binary_pairing_symmetric (β g).toAdd (α h).toAdd]
  calc
    _ = -binaryPairing (α g).toAdd (β h).toAdd-binaryPairing (α h).toAdd (β g).toAdd := by abel
    _ = _ := by rw [actual_binary_neg]

lemma actual_binary_cross_cochain_locally_constant [TopologicalSpace G]
    (α β : G →* Multiplicative BinaryPlane) (hα : IsLocallyConstant α) (hβ : IsLocallyConstant β) :
    IsLocallyConstant (binaryCrossCochain α β) :=
  (hα.prodMk hβ).comp (fun z => binaryPairing z.1.toAdd z.2.toAdd)

lemma actual_binary_cup_class_symmetric (α β : G →* Multiplicative BinaryPlane) :
    binaryCupClass α β=binaryCupClass β α := by
  apply (H2π_eq_iff _ _).mpr
  exact ⟨binaryCrossCochain α β,actual_binary_cross_boundary α β⟩

end ActualTwoDescentBinaryCupBoundaries318
