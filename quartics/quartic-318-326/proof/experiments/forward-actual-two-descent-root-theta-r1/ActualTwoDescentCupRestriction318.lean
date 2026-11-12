module
public import ActualTwoDescentOriginalContinuousCup318
public import ActualTwoDescentTorsionTransferCoordinates318
public import ActualTwoDescentContinuousCocycleRestriction318
public section
noncomputable section
namespace ActualTwoDescentCupRestriction318
open ActualTwoDescentSquareOneBinary318 ActualTwoDescentBinarySymplectic318
open ActualTwoDescentBinaryCupCocycles318 ActualTwoDescentBinaryCupBoundaries318
open ActualTwoDescentOriginalTorsionPairing318 ActualTwoDescentOriginalContinuousCup318
open ActualTwoDescentFieldSquareOneUnits318 ActualTwoDescentFieldSquareOneMaps318
open ActualTwoDescentTorsionTransferCoordinates318 ActualTwoDescentTorsionCoefficientTransfer318
open ActualTwoDescentFieldTorsionSignEquivalence318 ActualTwoDescentClosureFieldEmbedding318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentSquareClassFieldMap318
open groupCohomology

lemma actual_binary_bit_field_map {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
    (f : K →+* L) (u : SquareOne K) : squareOneBit (squareOneMap f u)=squareOneBit u := by
  rcases actual_square_one_cases u with rfl|rfl
  · rw [map_one,actual_bit_one,actual_bit_one]
  · have hneg : squareOneMap f (negativeOne : SquareOne K)=negativeOne := by
      apply Subtype.ext
      apply Units.ext
      change f (-1)= -1
      rw [map_neg,map_one]
    rw [hneg,actual_bit_negative,actual_bit_negative]

section Groups
variable {G H : Type*} [Group G] [Group H]

/-- The original cochain restriction, with the SAME coefficient F2. -/
def binaryCocycleRestriction (φ : H →* G) (z : cocycles₂ (binaryCoefficientRep G)) :
    cocycles₂ (binaryCoefficientRep H) :=
  ⟨fun gh => z (φ gh.1,φ gh.2),by
    apply (mem_cocycles₂_iff _).mpr
    intro g h j
    have hz := (mem_cocycles₂_iff z).mp z.property (φ g) (φ h) (φ j)
    simpa only [map_mul,Representation.isTrivial_apply] using hz⟩

lemma actual_binary_cup_restriction (φ : H →* G) (α β : G →* Multiplicative BinaryPlane) :
    binaryCocycleRestriction φ (binaryCupCocycle α β)=binaryCupCocycle (α.comp φ) (β.comp φ) := by
  apply Subtype.ext
  funext gh
  rfl

lemma actual_binary_boundary_restriction (φ : H →* G) (b : G → ZMod 2) :
    (fun gh : H × H => d₁₂ (binaryCoefficientRep G) b (φ gh.1,φ gh.2))=
      d₁₂ (binaryCoefficientRep H) (b ∘ φ) := by
  funext gh
  simp only [d₁₂_hom_apply,Representation.isTrivial_apply,Function.comp_apply,map_mul]

lemma actual_binary_restricted_cochain_continuous [TopologicalSpace G] [TopologicalSpace H]
    (φ : H →* G) (hφ : Continuous φ) (b : G → ZMod 2) (hb : IsLocallyConstant b) :
    IsLocallyConstant (b ∘ φ) := hb.comp_continuous hφ
end Groups

section Fields
variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _

lemma actual_original_torsion_binary_transfer (f : F →+* L) (n : F) (hn : n ≠ 0)
    (T : Multiplicative (closedTwoTorsion n)) :
    torsionBinaryEquiv (f n) (field_map_ne_zero f hn) (torsionCoefficientTransfer f n hn T).toAdd=
      torsionBinaryEquiv n hn T.toAdd := by
  change (squareOneBit (torsionSignEquiv (f n) (field_map_ne_zero f hn)
      (torsionCoefficientTransfer f n hn T)).1,
    squareOneBit (torsionSignEquiv (f n) (field_map_ne_zero f hn)
      (torsionCoefficientTransfer f n hn T)).2)=
    (squareOneBit (torsionSignEquiv n hn T).1,squareOneBit (torsionSignEquiv n hn T).2)
  rw [actual_torsion_transfer_signs]
  simp only [actual_binary_bit_field_map]

lemma actual_original_binary_character_restriction (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n) :
    originalBinaryCharacter (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ)=
      (originalBinaryCharacter n hn χ).comp (Field.absoluteGaloisGroup.map f).toMonoidHom := by
  apply MonoidHom.ext
  intro σ
  exact congrArg Multiplicative.ofAdd (actual_original_torsion_binary_transfer f n hn
    ((χ : Field.absoluteGaloisGroup F →* Multiplicative (closedTwoTorsion n))
      (Field.absoluteGaloisGroup.map f σ)))

/-- Genuine field restriction with the original Galois map and actual E[2]
coordinate transfer, hence applicable to every real and p-adic place. -/
theorem actual_original_cup_restriction (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n) :
    originalCupCocycle (f n) (field_map_ne_zero f hn)
      (cocycleRestriction f n hn χ) (cocycleRestriction f n hn ψ)=
    binaryCocycleRestriction (Field.absoluteGaloisGroup.map f).toMonoidHom
      (originalCupCocycle n hn χ ψ) := by
  unfold originalCupCocycle
  rw [actual_original_binary_character_restriction,actual_original_binary_character_restriction]
  exact (actual_binary_cup_restriction _ _ _).symm

end Fields
end ActualTwoDescentCupRestriction318
