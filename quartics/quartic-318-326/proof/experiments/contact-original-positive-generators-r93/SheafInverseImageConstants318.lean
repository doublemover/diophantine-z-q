module
public import StructureAdditiveSheaf318
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian

public section
noncomputable section
namespace SheafInverseImageConstants318
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : TopCat.{0}} (f : X ⟶ Y)

abbrev inverseImage := (Opens.map f).sheafPullback AddCommGrpCat.{0}
  (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
abbrev directImage := (Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{0}
  (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
abbrev adjunction := (Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{0}
  (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
abbrev globalSections (X : TopCat.{0}) :=
  (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)
abbrev constantFunctor (X : TopCat.{0}) :=
  constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}

instance inverseImage_limits : PreservesFiniteLimits (inverseImage f) := by
  unfold inverseImage
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits
instance inverseImage_colimits : PreservesFiniteColimits (inverseImage f) := by
  let := (adjunction f).isLeftAdjoint
  infer_instance
instance inverseImage_additive : (inverseImage f).Additive := Functor.additive_of_preserves_binary_products _

instance directImage_limits : PreservesFiniteLimits (directImage f) := by
  let := (adjunction f).isRightAdjoint
  infer_instance
instance directImage_additive : (directImage f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Direct-image global sections are the original source global sections. -/
@[expose] def directImageGlobalSections :
    directImage f ⋙ globalSections Y ≅ globalSections X :=
  Iso.refl _

/-- Inverse image preserves the actual constant sheaf, via the adjunctions with Γ. -/
@[expose] def inverseImageConstantIso :
    constantFunctor Y ⋙ inverseImage f ≅ constantFunctor X :=
  Adjunction.leftAdjointUniq
    (((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop).comp
      (adjunction f)).ofNatIsoRight (directImageGlobalSections f))
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop)

abbrev integerSheaf (X : TopCat.{0}) := (constantFunctor X).obj (AddCommGrpCat.of (ULift ℤ))
@[expose] def integerIso : (inverseImage f).obj (integerSheaf Y) ≅ integerSheaf X :=
  (inverseImageConstantIso f).app _

end SheafInverseImageConstants318
