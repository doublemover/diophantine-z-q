module
public import AffinePullbackStructure318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace AffineFaithfullyFlatChart318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 2200000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
  (U : Y.Opens) (hU : IsAffineOpen U)

/-- The whole inverse image of the original affine base open is used. -/
abbrev source := (hU.preimage f).fromSpec
abbrev base := hU.fromSpec
abbrev map := Spec.map (f.app U)

lemma square : source f U hU ≫ f = map f U ≫ base U hU :=
  (AffinePullbackStructure318.square f U hU).w.symm

include hU in
/-- Faithful flatness is derived for the exact original section-ring map,
not for an unrelated affine presentation or a selected source subchart. -/
lemma ring_faithfullyFlat [Flat f] [Surjective f] : (f.app U).hom.FaithfullyFlat := by
  apply (flat_and_surjective_SpecMap_iff (f.app U)).mp
  exact ⟨MorphismProperty.of_isPullback (AffinePullbackStructure318.square f U hU).flip
      (inferInstance : Flat f),
    MorphismProperty.of_isPullback (AffinePullbackStructure318.square f U hU).flip
      (inferInstance : Surjective f)⟩

/-- The algebra structure is exactly the original map f.app U. -/
abbrev algebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra

include hU in
lemma module_faithfullyFlat [Flat f] [Surjective f] :
    letI := algebra f U
    Module.FaithfullyFlat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  letI := algebra f U
  exact RingHom.faithfullyFlat_algebraMap_iff.mp (ring_faithfullyFlat f U hU)

end AffineFaithfullyFlatChart318
