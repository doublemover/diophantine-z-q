module
public import ActualTwoDescentOriginalTorsionPairing318
public section
noncomputable section
namespace ActualTwoDescentBinaryCupCocycles318
open ActualTwoDescentBinarySymplectic318
open groupCohomology
variable {G : Type*} [Group G]

abbrev binaryCoefficientRep (G : Type*) [Group G] : Rep ℤ G := Rep.trivial ℤ G (ZMod 2)

def binaryCup (α β : G →* Multiplicative BinaryPlane) (g : G × G) : ZMod 2 :=
  binaryPairing (α g.1).toAdd (β g.2).toAdd

lemma actual_binary_cup_cocycle (α β : G →* Multiplicative BinaryPlane) :
    binaryCup α β ∈ cocycles₂ (binaryCoefficientRep G) := by
  apply (mem_cocycles₂_iff _).mpr
  intro g h j
  rw [Representation.isTrivial_apply]
  simp only [binaryCup,map_mul]
  change binaryPairing ((α g).toAdd+(α h).toAdd) (β j).toAdd+
    binaryPairing (α g).toAdd (β h).toAdd =
    binaryPairing (α h).toAdd (β j).toAdd+
    binaryPairing (α g).toAdd ((β h).toAdd+(β j).toAdd)
  rw [actual_binary_pairing_add_left,actual_binary_pairing_add_right]
  abel

def binaryCupCocycle (α β : G →* Multiplicative BinaryPlane) : cocycles₂ (binaryCoefficientRep G) :=
  ⟨binaryCup α β,actual_binary_cup_cocycle α β⟩

def binaryCupClass (α β : G →* Multiplicative BinaryPlane) : H2 (binaryCoefficientRep G) :=
  H2π (binaryCoefficientRep G) (binaryCupCocycle α β)

lemma actual_binary_cup_locally_constant [TopologicalSpace G]
    (α β : G →* Multiplicative BinaryPlane) (hα : IsLocallyConstant α) (hβ : IsLocallyConstant β) :
    IsLocallyConstant (binaryCup α β) :=
  ((hα.comp_continuous continuous_fst).prodMk (hβ.comp_continuous continuous_snd)).comp
    (fun z => binaryPairing z.1.toAdd z.2.toAdd)

lemma actual_binary_cup_add_left (α α' β : G →* Multiplicative BinaryPlane) :
    binaryCupCocycle (α*α') β=binaryCupCocycle α β+binaryCupCocycle α' β := by
  apply Subtype.ext
  funext g
  exact actual_binary_pairing_add_left (α g.1).toAdd (α' g.1).toAdd (β g.2).toAdd

lemma actual_binary_cup_add_right (α β β' : G →* Multiplicative BinaryPlane) :
    binaryCupCocycle α (β*β')=binaryCupCocycle α β+binaryCupCocycle α β' := by
  apply Subtype.ext
  funext g
  exact actual_binary_pairing_add_right (α g.1).toAdd (β g.2).toAdd (β' g.2).toAdd

lemma actual_binary_cup_class_add_left (α α' β : G →* Multiplicative BinaryPlane) :
    binaryCupClass (α*α') β=binaryCupClass α β+binaryCupClass α' β := by
  rw [binaryCupClass,actual_binary_cup_add_left,map_add]
  rfl

lemma actual_binary_cup_class_add_right (α β β' : G →* Multiplicative BinaryPlane) :
    binaryCupClass α (β*β')=binaryCupClass α β+binaryCupClass α β' := by
  rw [binaryCupClass,actual_binary_cup_add_right,map_add]
  rfl

end ActualTwoDescentBinaryCupCocycles318
