module
public import ActualTwoDescentBinaryCupBoundaries318
public section
noncomputable section
namespace ActualTwoDescentOriginalContinuousCup318
open ActualTwoDescentOriginalTorsionPairing318 ActualTwoDescentBinarySymplectic318
open ActualTwoDescentBinaryCupCocycles318 ActualTwoDescentBinaryCupBoundaries318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentContinuousHOneEmbedding318 groupCohomology
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Gal" => Field.absoluteGaloisGroup F

def originalBinaryCharacter (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    Gal →* Multiplicative BinaryPlane where
  toFun σ := Multiplicative.ofAdd (torsionBinaryEquiv n hn ((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd)
  map_one' := by simp
  map_mul' σ τ := by
    change Multiplicative.ofAdd (torsionBinaryEquiv n hn ((χ : Gal →* Multiplicative (closedTwoTorsion n)) (σ*τ)).toAdd)=_
    rw [map_mul]
    exact congrArg Multiplicative.ofAdd ((torsionBinaryEquiv n hn).map_add _ _)

lemma actual_original_binary_character_locally_constant (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n) : IsLocallyConstant (originalBinaryCharacter n hn χ) :=
  χ.property.comp (fun T => Multiplicative.ofAdd (torsionBinaryEquiv n hn T.toAdd))

lemma actual_original_binary_character_mul (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n) :
    originalBinaryCharacter n hn (χ*ψ)=originalBinaryCharacter n hn χ*originalBinaryCharacter n hn ψ := by
  apply MonoidHom.ext
  intro σ
  exact congrArg Multiplicative.ofAdd ((torsionBinaryEquiv n hn).map_add _ _)

def originalCupCocycle (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    cocycles₂ (binaryCoefficientRep Gal) :=
  binaryCupCocycle (originalBinaryCharacter n hn χ) (originalBinaryCharacter n hn ψ)

def originalCupClass (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    H2 (binaryCoefficientRep Gal) :=
  H2π (binaryCoefficientRep Gal) (originalCupCocycle n hn χ ψ)

/-- The constructed cochain uses the ACTUAL torsion values at the ACTUAL
Galois elements, rather than independent finite-coordinate proxies. -/
lemma actual_original_cup_value (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) (σ τ : Gal) :
    originalCupCocycle n hn χ ψ (σ,τ)=originalTorsionPairing n hn
      (((χ : Gal →* Multiplicative (closedTwoTorsion n)) σ).toAdd)
      (((ψ : Gal →* Multiplicative (closedTwoTorsion n)) τ).toAdd) := rfl

lemma actual_original_cup_locally_constant (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    IsLocallyConstant (originalCupCocycle n hn χ ψ) :=
  actual_binary_cup_locally_constant _ _
    (actual_original_binary_character_locally_constant n hn χ)
    (actual_original_binary_character_locally_constant n hn ψ)

lemma actual_original_cup_class_mul_left (n : F) (hn : n ≠ 0) (χ χ' ψ : continuousCocycles n) :
    originalCupClass n hn (χ*χ') ψ=originalCupClass n hn χ ψ+originalCupClass n hn χ' ψ := by
  change binaryCupClass (originalBinaryCharacter n hn (χ*χ')) (originalBinaryCharacter n hn ψ)=_
  rw [actual_original_binary_character_mul,actual_binary_cup_class_add_left]
  rfl

lemma actual_original_cup_class_mul_right (n : F) (hn : n ≠ 0) (χ ψ ψ' : continuousCocycles n) :
    originalCupClass n hn χ (ψ*ψ')=originalCupClass n hn χ ψ+originalCupClass n hn χ ψ' := by
  change binaryCupClass (originalBinaryCharacter n hn χ) (originalBinaryCharacter n hn (ψ*ψ'))=_
  rw [actual_original_binary_character_mul,actual_binary_cup_class_add_right]
  rfl

lemma actual_original_cup_class_alternating (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    originalCupClass n hn χ χ=0 := actual_binary_cup_class_alternating _

lemma actual_original_cup_class_symmetric (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    originalCupClass n hn χ ψ=originalCupClass n hn ψ χ := actual_binary_cup_class_symmetric _ _

/-- No representative dependence is hidden: equality in the original
native H1 forces equality of its actual continuous representatives. -/
lemma actual_original_cup_respects_hone (n : F) (hn : n ≠ 0)
    (χ χ' ψ ψ' : continuousCocycles n)
    (hχ : continuousHOneMap n χ=continuousHOneMap n χ')
    (hψ : continuousHOneMap n ψ=continuousHOneMap n ψ') :
    originalCupClass n hn χ ψ=originalCupClass n hn χ' ψ' := by
  rw [actual_continuous_hone_injective n hχ,actual_continuous_hone_injective n hψ]

/-- Both self-cup and skew-symmetry use explicitly LOCALLY CONSTANT
bounding cochains. No comparison of continuous and abstract H2 is asserted. -/
theorem actual_original_continuous_self_boundary (n : F) (hn : n ≠ 0) (χ : continuousCocycles n) :
    ∃ b : Gal → ZMod 2, IsLocallyConstant b ∧
      d₁₂ (binaryCoefficientRep Gal) b=(originalCupCocycle n hn χ χ : Gal × Gal → ZMod 2) :=
  ⟨binarySelfCochain (originalBinaryCharacter n hn χ),
    actual_binary_self_cochain_locally_constant _ (actual_original_binary_character_locally_constant n hn χ),
    actual_binary_self_cup_boundary _⟩

end ActualTwoDescentOriginalContinuousCup318
